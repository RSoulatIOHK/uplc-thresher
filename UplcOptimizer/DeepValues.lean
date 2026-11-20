import PlutusCore.UPLC.CekMachine

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.BuiltinFunctions.Evaluate
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

mutual
  /-- A term correspondence lifted to values and captured environments. -/
  inductive ValueRel (R : Term → Term → Prop) : CekValue → CekValue → Prop where
    | const {constant} : ValueRel R (.VCon constant) (.VCon constant)
    | lam {left right leftEnv rightEnv} : R left right → ValueListRel R leftEnv rightEnv →
        ValueRel R (.VLam left leftEnv) (.VLam right rightEnv)
    | delay {left right leftEnv rightEnv} : R left right → ValueListRel R leftEnv rightEnv →
        ValueRel R (.VDelay left leftEnv) (.VDelay right rightEnv)
    | constr {tag left right} : ValueListRel R left right →
        ValueRel R (.VConstr tag left) (.VConstr tag right)
    | builtin {builtin left right expected} : ValueListRel R left right →
        ValueRel R (.VBuiltin builtin left expected) (.VBuiltin builtin right expected)

  inductive ValueListRel (R : Term → Term → Prop) : List CekValue → List CekValue → Prop where
    | nil : ValueListRel R [] []
    | cons {left right leftTail rightTail} :
        ValueRel R left right → ValueListRel R leftTail rightTail →
        ValueListRel R (left :: leftTail) (right :: rightTail)
end

inductive ValueOptionRel (R : Term → Term → Prop) : Option CekValue → Option CekValue → Prop where
  | none : ValueOptionRel R none none
  | some {left right} : ValueRel R left right → ValueOptionRel R (some left) (some right)

variable {R : Term → Term → Prop}

theorem ValueListRel.lookup {left right} (related : ValueListRel R left right) (index : Nat) :
    ValueOptionRel R left[index]? right[index]? := by
  match related, index with
  | .nil, _ => exact .none
  | .cons head _, 0 => exact .some head
  | .cons _ tail, index + 1 => exact tail.lookup index

theorem ValueListRel.length {left right} (related : ValueListRel R left right) :
    left.length = right.length := by
  match related with
  | .nil => rfl
  | .cons _ tail => simp only [List.length_cons, tail.length]

theorem ValueListRel.append {left right leftTail rightTail} (related : ValueListRel R left right)
    (tail : ValueListRel R leftTail rightTail) :
    ValueListRel R (left ++ leftTail) (right ++ rightTail) := by
  match related with
  | .nil => exact tail
  | .cons head rest => exact .cons head (rest.append tail)

theorem ValueListRel.reverse {left right} (related : ValueListRel R left right) :
    ValueListRel R left.reverse right.reverse := by
  match related with
  | .nil => exact .nil
  | .cons head tail =>
    rw [List.reverse_cons, List.reverse_cons]
    exact tail.reverse.append (.cons head .nil)

private theorem ValueOptionRel.bindSame {α : Type} (input : Option α)
    {left right : α → Option CekValue}
    (related : ∀ value, ValueOptionRel R (left value) (right value)) :
    ValueOptionRel R (input.bind left) (input.bind right) := by
  cases input with
  | none => exact .none
  | some value => exact related value

private theorem ValueOptionRel.mapSame {α : Type} (input : Option α)
    {left right : α → CekValue}
    (related : ∀ value, ValueRel R (left value) (right value)) :
    ValueOptionRel R (input.map left) (input.map right) := by
  cases input with
  | none => exact .none
  | some value => exact .some (related value)

open Lean Meta Elab Tactic in
private partial def countValueArguments (args : Expr) : MetaM Nat := do
  let args ← whnf args
  let fields := args.getAppArgs
  let count := if (← whnf fields[0]!).isConstOf ``ExpectedBuiltinArg.ArgV then 1 else 0
  if args.getAppFn.isConstOf ``ExpectedBuiltinArgs.More then
    return count + (← countValueArguments fields[1]!)
  return count

open Lean Meta Elab Tactic in
private def closeSimpleBuiltin : TacticM Bool := do
  let saved ← saveState
  let done ← withoutRecover <| tryTactic (evalTactic (← `(tactic|
    first
    | exact ValueOptionRel.none
    | exact ValueOptionRel.some ValueRel.const
    | exact ValueOptionRel.some (by assumption))))
  unless done do saved.restore
  return done

open Lean Meta Elab Tactic in
private partial def proveBuiltinResult (fuel : Nat := 15) : TacticM Unit := do
  if ← closeSimpleBuiltin then return
  evalTactic (← `(tactic| try simp_all [Option.bind, Option.map, Function.comp_def]))
  if (← getGoals).isEmpty then return
  if ← closeSimpleBuiltin then return
  if fuel == 0 then throwError "too many cases proving the builtin result: {← getMainTarget}"
  let target ← getMainTarget
  let subgoals ← evalTacticAt (← `(tactic|
    first
    | apply ValueOptionRel.bindSame
      intro value
    | exact ValueOptionRel.mapSame _ (fun _ => ValueRel.const)
    | split)) (← getMainGoal)
  for subgoal in subgoals do
    setGoals [subgoal]
    if (← getMainTarget) == target then
      throwError "builtin result proof did not progress: {target}"
    proveBuiltinResult (fuel - 1)
  setGoals []

open Lean Meta Elab Tactic in
private partial def proveBuiltinInputs (heads : List Expr) : TacticM Unit := do
  if ← closeSimpleBuiltin then return
  match heads with
  | [] => proveBuiltinResult
  | head :: rest =>
    for branch in ← (← getMainGoal).cases head.fvarId! do
      setGoals [branch.mvarId]
      proveBuiltinInputs (rest.map branch.subst.apply)
    setGoals []

open Lean Meta Elab Tactic in
private partial def proveBuiltinArguments (selector : Bool) (remaining : Nat) (tail : Expr)
    (heads : List Expr) : TacticM Unit := do
  for branch in ← (← getMainGoal).cases tail.fvarId! do
    setGoals [branch.mvarId]
    let heads := heads.map branch.subst.apply
    if branch.ctorName == ``ValueListRel.nil then
      proveBuiltinInputs (if selector && remaining == 0 then heads.take 1 else heads.reverse)
    else
      let head := branch.fields[branch.fields.size - 2]!
      let tail := branch.fields.back!
      if remaining == 0 then
        proveBuiltinInputs (if selector then heads.take 1 else (head :: heads).reverse)
      else
        proveBuiltinArguments selector (remaining - 1) tail (head :: heads)
  setGoals []

open Lean Meta Elab Tactic in
private def evalRelatedBuiltin (related : FVarId) : TacticM Unit := withMainContext do
  let builtin := (← getMainTarget).getAppArgs[1]!.getAppArgs[1]!
  let expected ← mkAppM ``expectedArgs #[builtin]
  let arity ← countValueArguments expected
  let selectors := [``BuiltinFun.IfThenElse, ``BuiltinFun.ChooseUnit, ``BuiltinFun.Trace,
    ``BuiltinFun.ChooseList, ``BuiltinFun.ChooseData]
  evalTactic (← `(tactic| simp only [evaluateBuiltinFunction]))
  let implementation := (← getMainTarget).getAppArgs[1]!.getAppFn.constName!
  evalTactic (← `(tactic| unfold $(mkIdent implementation)))
  evalTactic (← `(tactic| try simp only [PlutusCore.UPLC.BuiltinFunctions.Utils.tryCatchSome, Option.map, Option.bind,
    Except.toOption, Function.comp_def, PlutusCore.Bool.ifThenElse, PlutusCore.Unit.chooseUnit,
    PlutusCore.Trace.trace]))
  proveBuiltinArguments (selectors.contains builtin.constName!) arity (.fvar related) []

open Lean Meta Elab Tactic in
elab "prove_builtin_relation " related:ident : tactic => withMainContext do
  withoutRecover <| evalRelatedBuiltin (← getFVarId related)

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
/-- Related arguments preserve the result of every builtin. The polymorphic
selectors return related input values, while other builtins compute from
equal constant payloads or fail in both runs. -/
theorem builtin_related (variant : BuiltinSemanticsVariant) (builtin : BuiltinFun)
    {inputs outputs} (related : ValueListRel R inputs outputs) :
    ValueOptionRel R (evaluateBuiltinFunction variant builtin inputs)
      (evaluateBuiltinFunction variant builtin outputs) := by
  cases builtin <;> prove_builtin_relation related

end UplcOptimizer.Deep
