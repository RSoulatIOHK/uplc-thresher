import PlutusCore.UPLC.Term

namespace UplcOptimizer

open PlutusCore.UPLC.Term

/-- Counts syntax nodes, including list children in constructors and cases. -/
partial def nodes : Term → Nat
  | .Lam body | .Delay body | .Force body => 1 + nodes body
  | .Apply fn arg => 1 + nodes fn + nodes arg
  | .Constr _ fields => fields.foldl (fun n field => n + nodes field) 1
  | .Case scrutinee branches =>
      branches.foldl (fun n branch => n + nodes branch) (1 + nodes scrutinee)
  | _ => 1

private partial def liftIndices (byAmount cutoff : Nat) : Term → Term
  | .Var index => .Var (if index < cutoff then index else index + byAmount)
  | .Lam body => .Lam (liftIndices byAmount (cutoff + 1) body)
  | .Delay body => .Delay (liftIndices byAmount cutoff body)
  | .Force body => .Force (liftIndices byAmount cutoff body)
  | .Apply fn arg => .Apply (liftIndices byAmount cutoff fn) (liftIndices byAmount cutoff arg)
  | .Constr tag fields => .Constr tag (fields.map (liftIndices byAmount cutoff))
  | .Case scrutinee branches =>
      .Case (liftIndices byAmount cutoff scrutinee) (branches.map (liftIndices byAmount cutoff))
  | term => term

/-- Substitute the argument while removing its lambda's binder. -/
private partial def substitute (argument : Term) (depth : Nat) : Term → Term
  | .Var index =>
      if index == depth then
        if depth == 0 then argument else liftIndices depth 0 argument
      else
        .Var (if index < depth then index else index - 1)
  | .Lam body => .Lam (substitute argument (depth + 1) body)
  | .Delay body => .Delay (substitute argument depth body)
  | .Force body => .Force (substitute argument depth body)
  | .Apply fn arg => .Apply (substitute argument depth fn) (substitute argument depth arg)
  | .Constr tag fields => .Constr tag (fields.map (substitute argument depth))
  | .Case scrutinee branches =>
      .Case (substitute argument depth scrutinee) (branches.map (substitute argument depth))
  | term => term

private structure Uses where
  count : Nat
  deferred : Bool
  deriving Inhabited

private def Uses.add (a b : Uses) : Uses :=
  { count := min 3 (a.count + b.count), deferred := a.deferred || b.deferred }

private partial def uses (depth : Nat) (deferred : Bool) : Term → Uses
  | .Var index =>
      if index == depth then ⟨1, deferred⟩ else ⟨0, false⟩
  | .Lam body => uses (depth + 1) true body
  | .Delay body => uses depth true body
  | .Force body => uses depth deferred body
  | .Apply fn arg => (uses depth deferred fn).add (uses depth deferred arg)
  | .Constr _ fields =>
      fields.foldl (fun total t => total.add (uses depth deferred t)) ⟨0, false⟩
  | .Case scrutinee branches =>
      branches.foldl (fun total t => total.add (uses depth deferred t))
        (uses depth deferred scrutinee)
  | _ => ⟨0, false⟩

/-- These forms evaluate without running a builtin or any enclosed code.
    An in-scope variable refers to an already evaluated value. -/
private def isValue (depth : Nat) : Term → Bool
  | .Var index => index < depth
  | .Const _ | .Builtin _ | .Lam _ | .Delay _ | .Constr _ [] => true
  | _ => false

private def isCheapToCopy : Term → Bool
  | .Var _ | .Const (.Bool _) | .Const .Unit => true
  | .Const (.Integer n) => n.natAbs < 128
  | _ => false

/-- A single use may absorb a strict argument if the use is reached before
    any computation that can fail, diverge, or emit a trace. -/
private partial def demandsBinderFirst (depth : Nat) : Term → Bool
  | .Var index => index == 0
  | .Apply fn arg => demandsBinderFirst depth fn ||
      (isValue depth fn && demandsBinderFirst depth arg)
  | .Force body | .Case body _ => demandsBinderFirst depth body
  | .Constr _ fields =>
      match fields.dropWhile (fun field => isValue depth field &&
          !demandsBinderFirst depth field) with
      | field :: _ => demandsBinderFirst depth field
      | [] => false
  | _ => false

private def foldIntegerBinary (builtin : BuiltinFun) (a b : Int) : Option Const :=
  match builtin with
  | .AddInteger => some (.Integer (a + b))
  | .SubtractInteger => some (.Integer (a - b))
  | .MultiplyInteger => some (.Integer (a * b))
  | .EqualsInteger => some (.Bool (a == b))
  | .LessThanInteger => some (.Bool (decide (a < b)))
  | .LessThanEqualsInteger => some (.Bool (decide (a ≤ b)))
  | _ => none

private def rewrite (depth : Nat) (term : Term) : Option (String × Term) :=
  match term with
  | .Force (.Delay body) => some ("force-delay", body)
  | .Apply (.Lam (.Var 0)) arg => some ("identity", arg)
  | .Force .Error | .Apply .Error _ | .Apply (.Lam _) .Error | .Case .Error _ =>
      some ("propagate-error", .Error)
  | .Apply (.Lam body) arg =>
      let use := uses 0 false body
      if isValue depth arg then
        if use.count == 0 || (use.count == 1 && !use.deferred) ||
            (use.count ≤ 2 && isCheapToCopy arg) then
          some (if use.count == 0 then "dead-value-binding" else "beta-value",
            substitute arg 0 body)
        else none
      else if use.count == 1 && demandsBinderFirst (depth + 1) body then
        some ("inline-strict-use", substitute arg 0 body)
      else none
  | .Case (.Constr tag fields) branches => do
      if !fields.isEmpty && !fields.all (isValue depth) then none else
        let branch ← branches[tag]?
        let result := fields.foldl Term.Apply branch
        -- A large constructor's case instruction can be more compact than applications.
        if fields.length ≤ 2 then some ("case-constructor", result) else none
  | .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) (.Const (.Bool cond))) yes) no =>
      if cond && isValue depth no then some ("select-branch", yes)
      else if !cond && isValue depth yes then some ("select-branch", no)
      else none
  | .Apply (.Apply (.Builtin builtin) (.Const (.Integer a))) (.Const (.Integer b)) => do
      let result ← foldIntegerBinary builtin a b
      some ("fold-integer", .Const result)
  | _ => none

structure Stats where
  rewrites : Nat := 0
  sweeps : Nat := 0
  byRule : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Contract all exposed root redexes, with a bound per approach to a node.
    A subsequent sweep finds redexes introduced inside a substitution. -/
private def contract (depth : Nat) : Nat → Term → StateM Stats Term
  | 0, term => pure term
  | fuel + 1, term => do
      let some (rule, replacement) := rewrite depth term | return term
      modify fun stats => { stats with
        rewrites := stats.rewrites + 1
        byRule := stats.byRule.insert rule (stats.byRule.getD rule 0 + 1) }
      contract depth fuel replacement

private partial def sweep (depth : Nat) (term : Term) : StateM Stats Term := do
  let rebuilt ← match term with
    | .Lam body => pure (.Lam (← sweep (depth + 1) body))
    | .Delay body => pure (.Delay (← sweep depth body))
    | .Force body => pure (.Force (← sweep depth body))
    | .Apply fn arg => pure (.Apply (← sweep depth fn) (← sweep depth arg))
    | .Constr tag fields => pure (.Constr tag (← fields.mapM (sweep depth)))
    | .Case scrutinee branches =>
        pure (.Case (← sweep depth scrutinee) (← branches.mapM (sweep depth)))
    | t => pure t
  contract depth 16 rebuilt

/-- Optimize a closed program without altering its declared UPLC version. -/
def optimize (program : Program) (maxSweeps : Nat := 12) : Program × Stats := Id.run do
  let .Program version body := program
  let mut result := body
  let mut stats : Stats := {}
  for _ in [:maxSweeps] do
    let (next, updated) := (sweep 0 result).run stats
    let done := updated.rewrites == stats.rewrites
    result := next
    stats := { updated with sweeps := stats.sweeps + 1 }
    if done then break
  return (.Program version result, stats)

end UplcOptimizer
