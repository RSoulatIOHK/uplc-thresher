import UplcOptimizer.DeepCode

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

private theorem StepRule.ofEval {lhs rhs : Term} (active : redex lhs = true)
    (advance : ∀ variant stack env, ∃ steps,
      stepN variant (steps + 1) (.Eval stack env lhs) = .Eval stack env rhs) :
    StepRule lhs rhs := by
  refine ⟨active, ?_⟩
  intro variant stack env
  obtain ⟨steps, entered⟩ := advance variant stack env
  let extra : Nat := if prepared rhs then 1 else 0
  refine ⟨steps + extra, ?_⟩
  have order : steps + extra + 1 = (steps + 1) + extra := by omega
  rw [order, stepN_add, entered]
  cases rhs <;> rfl

@[uplc_deep_rule] theorem cancelForceDelay (body : Term) :
    StepRule (.Force (.Delay body)) body :=
  .ofEval rfl (fun _ _ _ => ⟨2, rfl⟩)

@[uplc_deep_rule] theorem identityConst (c : Const) :
    StepRule (.Apply (.Lam (.Var 0)) (.Const c)) (.Const c) :=
  ⟨rfl, fun _ _ _ => ⟨5, rfl⟩⟩

@[uplc_deep_rule] theorem identityLambda (body : Term) :
    StepRule (.Apply (.Lam (.Var 0)) (.Lam body)) (.Lam body) :=
  ⟨rfl, fun _ _ _ => ⟨5, rfl⟩⟩

@[uplc_deep_rule] theorem identityDelay (body : Term) :
    StepRule (.Apply (.Lam (.Var 0)) (.Delay body)) (.Delay body) :=
  ⟨rfl, fun _ _ _ => ⟨5, rfl⟩⟩

@[uplc_deep_rule] theorem addLiterals (a b : Int) :
    StepRule (.Apply (.Apply (.Builtin .AddInteger) (.Const (.Integer a))) (.Const (.Integer b)))
      (.Const (.Integer (a + b))) :=
  ⟨rfl, fun _ _ _ => ⟨8, rfl⟩⟩

@[uplc_deep_rule] theorem subtractLiterals (a b : Int) :
    StepRule (.Apply (.Apply (.Builtin .SubtractInteger) (.Const (.Integer a))) (.Const (.Integer b)))
      (.Const (.Integer (a - b))) :=
  ⟨rfl, fun _ _ _ => ⟨8, rfl⟩⟩

@[uplc_deep_rule] theorem multiplyLiterals (a b : Int) :
    StepRule (.Apply (.Apply (.Builtin .MultiplyInteger) (.Const (.Integer a))) (.Const (.Integer b)))
      (.Const (.Integer (a * b))) :=
  ⟨rfl, fun _ _ _ => ⟨8, rfl⟩⟩

@[uplc_deep_rule] theorem equalLiterals (a b : Int) :
    StepRule (.Apply (.Apply (.Builtin .EqualsInteger) (.Const (.Integer a))) (.Const (.Integer b)))
      (.Const (.Bool (a == b))) :=
  ⟨rfl, fun _ _ _ => ⟨8, rfl⟩⟩

@[uplc_deep_rule] theorem lessThanLiterals (a b : Int) :
    StepRule (.Apply (.Apply (.Builtin .LessThanInteger) (.Const (.Integer a))) (.Const (.Integer b)))
      (.Const (.Bool (decide (a < b)))) :=
  ⟨rfl, fun _ _ _ => ⟨8, rfl⟩⟩

@[uplc_deep_rule] theorem lessThanEqualsLiterals (a b : Int) :
    StepRule (.Apply (.Apply (.Builtin .LessThanEqualsInteger) (.Const (.Integer a))) (.Const (.Integer b)))
      (.Const (.Bool (decide (a ≤ b)))) :=
  ⟨rfl, fun _ _ _ => ⟨8, rfl⟩⟩

@[uplc_deep_rule] theorem selectNullaryCase (tag : Nat) (branches : List Term) :
    StepRule (.Case (.Constr tag []) branches) (branches[tag]?.getD .Error) := by
  cases selected : branches[tag]? with
  | none =>
    refine ⟨rfl, fun variant stack env => ⟨2, ?_⟩⟩
    change (match List.get?Internal branches tag with
      | some body => State.Eval stack env body | none => State.Error) = State.Error
    simp only [List.get?Internal_eq_getElem?, selected]
  | some body =>
    apply StepRule.ofEval rfl
    intro variant stack env
    refine ⟨2, ?_⟩
    change (match List.get?Internal branches tag with
      | some found => State.Eval stack env found | none => State.Error) = State.Eval stack env body
    simp only [List.get?Internal_eq_getElem?, selected]

@[uplc_deep_rule] theorem selectDelayedBranch (condition : Bool) (yes no : Term) :
    StepRule (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) (.Const (.Bool condition)))
      (.Delay yes)) (.Delay no)) (.Delay (if condition then yes else no)) := by
  cases condition <;> exact ⟨rfl, fun _ _ _ => ⟨14, rfl⟩⟩

@[uplc_deep_rule] theorem forceError : StepRule (.Force .Error) .Error :=
  ⟨rfl, fun _ _ _ => ⟨1, rfl⟩⟩

@[uplc_deep_rule] theorem applyError (arg : Term) : StepRule (.Apply .Error arg) .Error :=
  ⟨rfl, fun _ _ _ => ⟨1, rfl⟩⟩

@[uplc_deep_rule] theorem applyLambdaToError (body : Term) :
    StepRule (.Apply (.Lam body) .Error) .Error :=
  ⟨rfl, fun _ _ _ => ⟨3, rfl⟩⟩

@[uplc_deep_rule] theorem caseError (branches : List Term) :
    StepRule (.Case .Error branches) .Error :=
  ⟨rfl, fun _ _ _ => ⟨1, rfl⟩⟩

def_uplc_deep_rules rootRule

end UplcOptimizer.Deep
