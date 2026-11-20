import PlutusCore.UPLC.CekMachine
import UplcOptimizer.TaggedRules

namespace UplcOptimizer

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- Iterate the CEK transition exactly `count` times. Terminal states are
absorbing under `step`, so this does not conflate exhaustion with failure. -/
def stepN (variant : BuiltinSemanticsVariant) : Nat → State → State
  | 0, state => state
  | count + 1, state => stepN variant count (step variant state)

theorem stepN_add (variant : BuiltinSemanticsVariant) (first second : Nat) (state : State) :
    stepN variant (first + second) state = stepN variant second (stepN variant first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, stepN]
  | succ first ih =>
    rw [Nat.succ_add]
    exact ih (step variant state)

/-- The two terms reach exactly the same state when evaluated in the same
environment and continuation. This is an observation about a term at the
head of an `Eval` state. Lifting it through arbitrary syntax contexts
requires a separate congruence proof. -/
def CekJoin (lhs rhs : Term) : Prop :=
  ∀ (variant : BuiltinSemanticsVariant) (stack : Stack) (env : Environment),
    ∃ (leftSteps rightSteps : Nat),
      stepN variant leftSteps (.Eval stack env lhs) =
        stepN variant rightSteps (.Eval stack env rhs)

theorem CekJoin.refl (term : Term) : CekJoin term term := by
  intro variant stack env
  exact ⟨0, 0, rfl⟩

theorem CekJoin.symm {lhs rhs : Term} (joined : CekJoin lhs rhs) : CekJoin rhs lhs := by
  intro variant stack env
  obtain ⟨leftSteps, rightSteps, same⟩ := joined variant stack env
  exact ⟨rightSteps, leftSteps, same.symm⟩

theorem CekJoin.trans {lhs middle rhs : Term} (left : CekJoin lhs middle)
    (right : CekJoin middle rhs) : CekJoin lhs rhs := by
  intro variant stack env
  obtain ⟨before, middleLeft, joinLeft⟩ := left variant stack env
  obtain ⟨middleRight, after, joinRight⟩ := right variant stack env
  refine ⟨before + middleRight, after + middleLeft, ?_⟩
  calc
    stepN variant (before + middleRight) (.Eval stack env lhs) =
        stepN variant middleRight (stepN variant before (.Eval stack env lhs)) :=
      stepN_add variant before middleRight _
    _ = stepN variant middleRight (stepN variant middleLeft (.Eval stack env middle)) :=
      congrArg (stepN variant middleRight) joinLeft
    _ = stepN variant (middleLeft + middleRight) (.Eval stack env middle) :=
      (stepN_add variant middleLeft middleRight _).symm
    _ = stepN variant (middleRight + middleLeft) (.Eval stack env middle) := by
      rw [Nat.add_comm middleLeft middleRight]
    _ = stepN variant middleLeft (stepN variant middleRight (.Eval stack env middle)) :=
      stepN_add variant middleRight middleLeft _
    _ = stepN variant middleLeft (stepN variant after (.Eval stack env rhs)) :=
      congrArg (stepN variant middleLeft) joinRight
    _ = stepN variant (after + middleLeft) (.Eval stack env rhs) :=
      (stepN_add variant after middleLeft _).symm

private theorem stepN_fixed (variant : BuiltinSemanticsVariant) (terminal : State)
    (fixed : step variant terminal = terminal) (count : Nat) :
    stepN variant count terminal = terminal := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [stepN, fixed] using ih

private theorem CekJoin.reaches {lhs rhs : Term} (joined : CekJoin lhs rhs)
    (variant : BuiltinSemanticsVariant) (stack : Stack) (env : Environment)
    {terminal : State} (fixed : step variant terminal = terminal)
    (reaches : ∃ count, stepN variant count (.Eval stack env lhs) = terminal) :
    ∃ count, stepN variant count (.Eval stack env rhs) = terminal := by
  obtain ⟨leftSteps, rightSteps, same⟩ := joined variant stack env
  obtain ⟨count, atTerminal⟩ := reaches
  refine ⟨rightSteps + count, ?_⟩
  calc
    stepN variant (rightSteps + count) (.Eval stack env rhs) =
        stepN variant count (stepN variant rightSteps (.Eval stack env rhs)) :=
      stepN_add variant rightSteps count _
    _ = stepN variant count (stepN variant leftSteps (.Eval stack env lhs)) :=
      congrArg (stepN variant count) same.symm
    _ = stepN variant (leftSteps + count) (.Eval stack env lhs) :=
      (stepN_add variant leftSteps count _).symm
    _ = stepN variant (count + leftSteps) (.Eval stack env lhs) := by
      rw [Nat.add_comm leftSteps count]
    _ = stepN variant leftSteps (stepN variant count (.Eval stack env lhs)) :=
      stepN_add variant count leftSteps _
    _ = terminal := by rw [atTerminal, stepN_fixed variant terminal fixed]

/-- A joined term reaches the same absorbing states, including errors and
successful returns, without requiring identical execution step counts. -/
theorem CekJoin.reaches_iff {lhs rhs : Term} (joined : CekJoin lhs rhs)
    (variant : BuiltinSemanticsVariant) (stack : Stack) (env : Environment)
    {terminal : State} (fixed : step variant terminal = terminal) :
    (∃ count, stepN variant count (.Eval stack env lhs) = terminal) ↔
      (∃ count, stepN variant count (.Eval stack env rhs) = terminal) :=
  ⟨joined.reaches variant stack env fixed, joined.symm.reaches variant stack env fixed⟩

/-- `some value` observes a successful halt and `none` observes a CEK error. -/
def observedState : Option CekValue → State
  | some value => .Halt value
  | none => .Error

private theorem observedState_fixed (variant : BuiltinSemanticsVariant) (result : Option CekValue) :
    step variant (observedState result) = observedState result := by
  cases result <;> rfl

private theorem runSteps_observed (variant : BuiltinSemanticsVariant) (result : Option CekValue)
    (count : Nat) (state : State) :
    (runSteps variant state count = observedState result) ↔
      (stepN variant count state = observedState result) := by
  induction count generalizing state with
  | zero => cases state <;> cases result <;> simp [runSteps, stepN, observedState]
  | succ count ih =>
    cases state with
    | Eval stack env term => exact ih (step variant (.Eval stack env term))
    | Return stack value => exact ih (step variant (.Return stack value))
    | Error => rw [stepN_fixed variant .Error rfl]; rfl
    | BudgetExhausted => rw [stepN_fixed variant .BudgetExhausted rfl]; rfl
    | Halt value => rw [stepN_fixed variant (.Halt value) rfl]; rfl

/-- For a common explicit argument list and UPLC version, the library's
evaluator can reach a given value or error on one side exactly when it can
reach that result on the other side. The two sufficient fuel counts can differ. -/
theorem CekJoin.programResult_iff {lhs rhs : Term} {args : List Term}
    (joined : CekJoin (applyParams lhs args) (applyParams rhs args))
    (variant : BuiltinSemanticsVariant) (version : Version) (result : Option CekValue) :
    (∃ count, cekExecuteProgramWithSemanticVariant variant (.Program version lhs) args count =
        observedState result) ↔
      (∃ count, cekExecuteProgramWithSemanticVariant variant (.Program version rhs) args count =
        observedState result) := by
  simp only [cekExecuteProgramWithSemanticVariant, initialState, runSteps_observed]
  exact joined.reaches_iff variant [] [] (observedState_fixed variant result)

@[uplc_rule] theorem forceDelay_join (body : Term) : CekJoin (.Force (.Delay body)) body := by
  intro variant stack env
  exact ⟨3, 0, rfl⟩

@[uplc_rule] theorem strictIdentityConst_join (constant : Const) :
    CekJoin (.Apply (.Lam (.Var 0)) (.Const constant)) (.Const constant) := by
  intro variant stack env
  exact ⟨6, 1, rfl⟩

@[uplc_rule] theorem addIntegerConst_join (left right : Int) :
    CekJoin (.Apply (.Apply (.Builtin .AddInteger) (.Const (.Integer left)))
      (.Const (.Integer right))) (.Const (.Integer (left + right))) := by
  intro variant stack env
  exact ⟨9, 1, rfl⟩

theorem caseNullaryConstr_join {tag : Nat} {branches : List Term} {branch : Term}
    (selected : branches[tag]? = some branch) :
    CekJoin (.Case (.Constr tag []) branches) branch := by
  intro variant stack env
  refine ⟨3, 0, ?_⟩
  change (match List.get?Internal branches tag with
    | some found => State.Eval stack env found
    | none => State.Error) = State.Eval stack env branch
  simp only [List.get?Internal_eq_getElem?, selected]

@[uplc_rule] theorem selectNullaryCase_join (tag : Nat) (branches : List Term) :
    CekJoin (.Case (.Constr tag []) branches) (branches[tag]?.getD .Error) := by
  cases selected : branches[tag]? with
  | some branch => exact caseNullaryConstr_join selected
  | none =>
    intro variant stack env
    refine ⟨3, 1, ?_⟩
    change (match List.get?Internal branches tag with
      | some found => State.Eval stack env found
      | none => State.Error) = State.Error
    simp only [List.get?Internal_eq_getElem?, selected]

end UplcOptimizer
