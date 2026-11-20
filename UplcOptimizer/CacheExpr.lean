import UplcOptimizer.LocalProofs

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.BuiltinFunctions.Evaluate
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- Unary builtins whose application protocol and result are independent of
the builtin semantics variant. A projection can still fail on the wrong input. -/
inductive CacheOp where
  | fstPair | sndPair | headList | tailList
  | unConstrData | unMapData | unListData | unIData | unBData

def CacheOp.builtin : CacheOp → BuiltinFun
  | .fstPair => .FstPair
  | .sndPair => .SndPair
  | .headList => .HeadList
  | .tailList => .TailList
  | .unConstrData => .UnConstrData
  | .unMapData => .UnMapData
  | .unListData => .UnListData
  | .unIData => .UnIData
  | .unBData => .UnBData

private def CacheOp.forces : CacheOp → Nat
  | .fstPair | .sndPair => 2
  | .headList | .tailList => 1
  | _ => 0

private def forceTimes : Nat → Term → Term
  | 0, term => term
  | count + 1, term => .Force (forceTimes count term)

def CacheOp.term (op : CacheOp) : Term := forceTimes op.forces (.Builtin op.builtin)

theorem CacheOp.evaluate (op : CacheOp) (variant : BuiltinSemanticsVariant) (args : List CekValue) :
    evaluateBuiltinFunction variant op.builtin args =
      evaluateBuiltinFunction default op.builtin args := by
  cases op <;> rfl

private theorem CacheOp.enter (op : CacheOp) (variant : BuiltinSemanticsVariant)
    (stack : Stack) (env : Environment) (arg : Term) :
    stepN variant (2 * op.forces + 3) (.Eval stack env (.Apply op.term arg)) =
      .Eval (.RightApplicationOfValue (.VBuiltin op.builtin [] (.One .ArgV)) :: stack) env arg := by
  cases op <;> rfl

private def CacheOp.match? : (term : Term) → Option { op : CacheOp // op.term = term }
  | .Force (.Force (.Builtin .FstPair)) => some ⟨.fstPair, rfl⟩
  | .Force (.Force (.Builtin .SndPair)) => some ⟨.sndPair, rfl⟩
  | .Force (.Builtin .HeadList) => some ⟨.headList, rfl⟩
  | .Force (.Builtin .TailList) => some ⟨.tailList, rfl⟩
  | .Builtin .UnConstrData => some ⟨.unConstrData, rfl⟩
  | .Builtin .UnMapData => some ⟨.unMapData, rfl⟩
  | .Builtin .UnListData => some ⟨.unListData, rfl⟩
  | .Builtin .UnIData => some ⟨.unIData, rfl⟩
  | .Builtin .UnBData => some ⟨.unBData, rfl⟩
  | _ => none

/-- Binder-free expressions with an exact finite CEK execution bound. -/
inductive CacheExpr where
  | var (index : Nat)
  | const (value : Const)
  | project (op : CacheOp) (arg : CacheExpr)

def CacheExpr.term : CacheExpr → Term
  | .var index => .Var index
  | .const value => .Const value
  | .project op arg => .Apply op.term arg.term

def CacheExpr.match? : (term : Term) → Option { expr : CacheExpr // expr.term = term }
  | .Var index => some ⟨.var index, rfl⟩
  | .Const value => some ⟨.const value, rfl⟩
  | .Apply fn arg => do
    let op ← CacheOp.match? fn
    let inner ← CacheExpr.match? arg
    return ⟨.project op.val inner.val, by
      change Term.Apply op.val.term inner.val.term = Term.Apply fn arg
      rw [op.property, inner.property]⟩
  | _ => none

def CacheExpr.eval (env : Environment) : CacheExpr → Option CekValue
  | .var index => env[index]?
  | .const value => some (.VCon value)
  | .project op arg => (arg.eval env).bind fun value =>
      evaluateBuiltinFunction default op.builtin [value]

def CacheExpr.shift : CacheExpr → CacheExpr
  | .var index => .var (index + 1)
  | .const value => .const value
  | .project op arg => .project op arg.shift

theorem CacheExpr.eval_shift (expr : CacheExpr) (value : CekValue) (env : Environment) :
    expr.shift.eval (value :: env) = expr.eval env := by
  induction expr with
  | var => rfl
  | const => rfl
  | project op arg ih => simp only [shift, eval, ih]

def CacheExpr.steps : CacheExpr → Nat
  | .var _ | .const _ => 1
  | .project op arg => 2 * op.forces + 3 + arg.steps + 1

theorem CacheExpr.steps_pos (expr : CacheExpr) : 0 < expr.steps := by
  cases expr <;> simp [CacheExpr.steps]

theorem CacheExpr.run (expr : CacheExpr) (variant : BuiltinSemanticsVariant)
    (stack : Stack) (env : Environment) :
    stepN variant expr.steps (.Eval stack env expr.term) =
      match expr.eval env with
      | some value => .Return stack value
      | none => .Error := by
  induction expr generalizing stack with
  | var =>
    simp only [steps, term, eval, stepN, step, List.get?Internal_eq_getElem?]
    rfl
  | const => rfl
  | project op arg ih =>
    simp only [steps, term, eval]
    rw [stepN_add, stepN_add, op.enter, ih]
    cases found : arg.eval env
    · rfl
    · simp [stepN, step, evalBuiltin, op.evaluate]
      rfl

/-- Execute the strict argument and enter the body of the new binding. -/
theorem CacheExpr.enterLet (expr : CacheExpr) (variant : BuiltinSemanticsVariant)
    (stack : Stack) (env : Environment) (body : Term) :
    stepN variant (expr.steps + 4) (.Eval stack env (.Apply (.Lam body) expr.term)) =
      match expr.eval env with
      | some value => .Eval stack (value :: env) body
      | none => .Error := by
  rw [show expr.steps + 4 = 3 + expr.steps + 1 by omega, stepN_add, stepN_add]
  change stepN variant 1
    (stepN variant expr.steps (.Eval (.RightApplicationOfValue (.VLam body env) :: stack) env
      expr.term)) = _
  rw [expr.run]
  cases expr.eval env <;> rfl

end UplcOptimizer.Deep
