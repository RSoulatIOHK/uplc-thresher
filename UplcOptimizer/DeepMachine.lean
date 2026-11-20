import UplcOptimizer.Application
import UplcOptimizer.Conditional
import UplcOptimizer.DeepValues
import PlutusCore.UPLC.CekMachine

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

private def ifConditionStack (stack : Stack) (env : Environment) (yes no : Term) : Stack :=
  .RightApplicationOfValue (.VBuiltin .IfThenElse []
    (.More .ArgV (.More .ArgV (.One .ArgV)))) ::
  .LeftApplicationToTerm yes env :: .LeftApplicationToTerm no env :: stack

inductive OptionRel {α : Type} (R : α → α → Prop) : Option α → Option α → Prop where
  | none : OptionRel R none none
  | some : R a b → OptionRel R (some a) (some b)

inductive ListRel {α : Type} (R : α → α → Prop) : List α → List α → Prop where
  | nil : ListRel R [] []
  | cons : R a b → ListRel R xs ys → ListRel R (a :: xs) (b :: ys)

theorem ListRel.length {α : Type} {R : α → α → Prop} {xs ys : List α}
    (related : ListRel R xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem ListRel.lookup {α : Type} {R : α → α → Prop} {xs ys : List α}
    (related : ListRel R xs ys) (idx : Nat) : OptionRel R xs[idx]? ys[idx]? := by
  induction related generalizing idx with
  | nil => exact .none
  | cons heads _ ih =>
    cases idx with
    | zero => exact .some heads
    | succ idx => exact ih idx

abbrev TermListRel (R : Layout → Term → Term → Prop) (layout : Layout) := ListRel (R layout)

inductive FrameRel (R : Layout → Term → Term → Prop) : Frame → Frame → Prop where
  | force : FrameRel R .ForceFrame .ForceFrame
  | leftTerm : R layout term term' → EnvRel R layout env env' →
      FrameRel R (.LeftApplicationToTerm term env) (.LeftApplicationToTerm term' env')
  | leftValue : ValueRel R value value' →
      FrameRel R (.LeftApplicationToValue value) (.LeftApplicationToValue value')
  | rightValue : ValueRel R value value' →
      FrameRel R (.RightApplicationOfValue value) (.RightApplicationOfValue value')
  | constructorArgument : ValueListRel R values values' → TermListRel R layout terms terms' →
      EnvRel R layout env env' →
      FrameRel R (.ConstructorArgument tag values terms env)
        (.ConstructorArgument tag values' terms' env')
  | caseScrutinee : TermListRel R layout branches branches' → EnvRel R layout env env' →
      FrameRel R (.CaseScrutinee branches env) (.CaseScrutinee branches' env')

inductive StackRel (R : Layout → Term → Term → Prop) : Stack → Stack → Prop where
  | nil : StackRel R [] []
  | cons : FrameRel R f f' → StackRel R s t → StackRel R (f :: s) (f' :: t)
  /-- The two evaluators are running the same argument of a saturated lambda
  spine. The source retains a final force; neither side executes it while
  any argument is still being evaluated. -/
  | saturatedDelay (rest : List Term) : StackRel R s t →
      EnvRel R .same captured captured' → EnvRel R .same arguments arguments' →
      R .same body body' → StackRel R
        (.RightApplicationOfValue (.VLam (lambdaPrefix rest.length (.Delay body)) captured) ::
          applicationFrames rest (.ForceFrame :: s) arguments)
        (.RightApplicationOfValue (.VLam (lambdaPrefix rest.length body') captured') ::
          applicationFrames rest t arguments')
  /-- The condition is still being evaluated on both sides. Only the source
  delays both arms and forces the selected result. -/
  | delayedIf : StackRel R s t → EnvRel R .same e e' →
      immediateArm yes = true → immediateArm no = true → StackRel R
      (ifConditionStack (.ForceFrame :: s) e (.Delay yes) (.Delay no))
      (ifConditionStack t e' yes no)

inductive StateRel (R : Layout → Term → Term → Prop) : State → State → Prop where
  | eval : StackRel R stack stack' → EnvRel R layout env env' → R layout term term' →
      StateRel R (.Eval stack env term) (.Eval stack' env' term')
  | ret : StackRel R stack stack' → ValueRel R value value' →
      StateRel R (.Return stack value) (.Return stack' value')
  | halt : ValueRel R value value' → StateRel R (.Halt value) (.Halt value')
  | error : StateRel R .Error .Error
  | budgetExhausted : StateRel R .BudgetExhausted .BudgetExhausted

variable {R : Layout → Term → Term → Prop}

private theorem evalBuiltin_related (variant : BuiltinSemanticsVariant) (builtin : BuiltinFun)
    (stacks : StackRel R s t) (values : ValueListRel R xs ys) :
    StateRel R (evalBuiltin variant s builtin xs) (evalBuiltin variant t builtin ys) := by
  unfold evalBuiltin
  have related := builtin_related variant builtin values
  generalize PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction variant builtin xs = left
    at related ⊢
  generalize PlutusCore.UPLC.BuiltinFunctions.Evaluate.evaluateBuiltinFunction variant builtin ys = right
    at related ⊢
  cases related with
  | none => exact .error
  | some value => exact .ret stacks value

private theorem apply_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (fns : ValueRel R fn fn') (args : ValueRel R arg arg') :
    StateRel R (step variant (.Return (.RightApplicationOfValue fn :: s) arg))
      (step variant (.Return (.RightApplicationOfValue fn' :: t) arg')) := by
  cases fns with
  | const => exact .error
  | delay => exact .error
  | lam bodies envs => exact .eval stacks (envs.push args) bodies
  | constr => exact .error
  | @builtin b xs ys expected values =>
    cases expected with
    | One kind =>
      cases kind with
      | ArgV => exact evalBuiltin_related variant b stacks (.cons args values)
      | ArgQ => exact .error
    | More kind rest =>
      cases kind with
      | ArgV => exact .ret stacks (.builtin (.cons args values))
      | ArgQ => exact .error

private theorem force_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (values : ValueRel R value value') :
    StateRel R (step variant (.Return (.ForceFrame :: s) value))
      (step variant (.Return (.ForceFrame :: t) value')) := by
  cases values with
  | const => exact .error
  | delay bodies envs => exact .eval stacks envs bodies
  | lam => exact .error
  | constr => exact .error
  | @builtin b xs ys expected values =>
    cases expected with
    | One kind =>
      cases kind with
      | ArgV => exact .error
      | ArgQ => exact evalBuiltin_related variant b stacks values
    | More kind rest =>
      cases kind with
      | ArgV => exact .error
      | ArgQ => exact .ret stacks (.builtin values)

private theorem folding_related (stacks : StackRel R s t) (values : ValueListRel R xs ys) :
    StackRel R (step.folding xs s) (step.folding ys t) := by
  match values with
  | .nil => exact stacks
  | .cons heads tail => exact .cons (.leftValue heads) (folding_related stacks tail)

private theorem branch_related (stacks : StackRel R s t) (envs : EnvRel R layout e e')
    (branches : TermListRel R layout bs bs') (idx : Nat) :
    StateRel R
      (match bs[idx]? with | some body => .Eval s e body | none => .Error)
      (match bs'[idx]? with | some body => .Eval t e' body | none => .Error) := by
  have related := branches.lookup idx
  generalize bs[idx]? = left at related ⊢
  generalize bs'[idx]? = right at related ⊢
  cases related with
  | none => exact .error
  | some bodies => exact .eval stacks envs bodies

private theorem StateRel.conditional {condition : Prop} [Decidable condition]
    (yes : StateRel R whenTrue whenTrue') (no : StateRel R whenFalse whenFalse') :
    StateRel R (if condition then whenTrue else whenFalse)
      (if condition then whenTrue' else whenFalse') := by
  by_cases h : condition
  · simpa only [if_pos h] using yes
  · simpa only [if_neg h] using no

private theorem literalFields_related (first second : Const) :
    ValueListRel R [.VCon first, .VCon second] [.VCon first, .VCon second] :=
  .cons .const (.cons .const .nil)

private theorem case_constant_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R layout e e') (branches : TermListRel R layout bs bs') (constant : Const) :
    StateRel R
      (step variant (.Return (.CaseScrutinee bs e :: s) (.VCon constant)))
      (step variant (.Return (.CaseScrutinee bs' e' :: t) (.VCon constant))) := by
  cases constant with
  | Integer n =>
    simp only [step, branches.length]
    exact StateRel.conditional (branch_related stacks envs branches n.toNat) .error
  | Bool b =>
    cases b <;> simp [step, List.get?Internal_eq_getElem?, branches.length]
    · exact StateRel.conditional (branch_related stacks envs branches 0) .error
    · exact StateRel.conditional (branch_related stacks envs branches 1) .error
  | Unit =>
    simp only [step, branches.length]
    exact StateRel.conditional (branch_related stacks envs branches 0) .error
  | Pair pair =>
    simp only [step, List.get?Internal_eq_getElem?, branches.length]
    exact StateRel.conditional
      (branch_related (folding_related stacks (literalFields_related pair.1 pair.2)) envs branches 0) .error
  | PairData pair =>
    simp only [step, List.get?Internal_eq_getElem?, branches.length]
    exact StateRel.conditional
      (branch_related (folding_related stacks (literalFields_related (.Data pair.1) (.Data pair.2)))
        envs branches 0) .error
  | ConstList items =>
    cases items <;> simp only [step, List.get?Internal_eq_getElem?, branches.length]
    · exact StateRel.conditional (branch_related stacks envs branches 1) .error
    · rename_i head tail
      exact StateRel.conditional
        (branch_related (folding_related stacks (literalFields_related head (.ConstList tail)))
          envs branches 0) .error
  | ConstDataList items =>
    cases items <;> simp only [step, List.get?Internal_eq_getElem?, branches.length]
    · exact StateRel.conditional (branch_related stacks envs branches 1) .error
    · rename_i head tail
      exact StateRel.conditional
        (branch_related (folding_related stacks (literalFields_related (.Data head) (.ConstDataList tail)))
          envs branches 0) .error
  | ConstPairDataList items =>
    cases items <;> simp only [step, List.get?Internal_eq_getElem?, branches.length]
    · exact StateRel.conditional (branch_related stacks envs branches 1) .error
    · rename_i head tail
      exact StateRel.conditional
        (branch_related (folding_related stacks
          (literalFields_related (.PairData head) (.ConstPairDataList tail))) envs branches 0) .error
  | _ => exact .error

private theorem case_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R layout e e') (branches : TermListRel R layout bs bs')
    (values : ValueRel R v w) :
    StateRel R (step variant (.Return (.CaseScrutinee bs e :: s) v))
      (step variant (.Return (.CaseScrutinee bs' e' :: t) w)) := by
  cases values with
  | @const c => exact case_constant_related variant stacks envs branches c
  | @constr tag _ _ fields =>
    simpa only [step, List.get?Internal_eq_getElem?] using
      branch_related (folding_related stacks fields) envs branches tag
  | lam => exact .error
  | delay => exact .error
  | builtin => exact .error

private theorem return_step_related (variant : BuiltinSemanticsVariant) (frames : FrameRel R f f')
    (stacks : StackRel R s t) (values : ValueRel R v w) :
    StateRel R (step variant (.Return (f :: s) v)) (step variant (.Return (f' :: t) w)) := by
  cases frames with
  | force => exact force_related variant stacks values
  | leftTerm terms envs => exact .eval (.cons (.rightValue values) stacks) envs terms
  | leftValue args => exact apply_related variant stacks values args
  | rightValue fns => exact apply_related variant stacks fns values
  | constructorArgument seen remaining envs =>
    cases remaining with
    | nil => exact .ret stacks (.constr (ValueListRel.cons values seen).reverse)
    | cons terms rest =>
      exact .eval (.cons (.constructorArgument (.cons values seen) rest envs) stacks) envs terms
  | caseScrutinee branches envs => exact case_related variant stacks envs branches values

private theorem delayed_if_return (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R .same e e') (condition : ValueRel R v w)
    (refl : ∀ term, R .same term term) {yes no : Term}
    (yesReady : immediateArm yes = true) (noReady : immediateArm no = true) :
    StateRel R
      (stepN variant 9 (.Return (ifConditionStack (.ForceFrame :: s) e (.Delay yes) (.Delay no)) v))
      (stepN variant 7 (.Return (ifConditionStack t e' yes no) w)) := by
  cases yes <;> cases no <;> simp only [immediateArm, Bool.false_eq_true] at yesReady noReady
  all_goals
    cases condition with
    | const =>
      rename_i c
      cases c <;> try exact .error
      rename_i b
      cases b <;> first
        | exact .ret stacks .const
        | exact .ret stacks (.lam (layout := .same) (refl _) envs)
        | exact .ret stacks (.delay (refl _) envs)
    | _ => exact .error

/-- A return transition preserves correspondence after one or more steps on
both sides. Saturated spines advance to the next argument or enter the body.
The delayed conditional resumes with the selected arm's value or an error. -/
theorem return_progress (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (values : ValueRel R v w) (refl : ∀ term, R .same term term) :
    ∃ n m, StateRel R (stepN variant (n + 1) (.Return s v))
      (stepN variant (m + 1) (.Return t w)) := by
  cases stacks with
  | nil => exact ⟨0, 0, .halt values⟩
  | cons frames stacks => exact ⟨0, 0, return_step_related variant frames stacks values⟩
  | saturatedDelay rest stacks captured arguments bodies =>
    cases rest with
    | nil => exact ⟨2, 0, .eval stacks (captured.push values) bodies⟩
    | cons arg rest =>
      exact ⟨2, 2, .eval (.saturatedDelay rest stacks (captured.push values) arguments bodies)
        arguments (refl arg)⟩
  | delayedIf stacks envs yesReady noReady =>
    exact ⟨8, 6, delayed_if_return variant stacks envs values refl yesReady noReady⟩

private theorem enterSaturatedCall (variant : BuiltinSemanticsVariant) (stack : Stack)
    (env : Environment) (body first : Term) (rest : List Term) :
    stepN variant ((first :: rest).length + 2)
      (.Eval stack env (applyParams (lambdaPrefix (rest.length + 1) body) (first :: rest))) =
      .Eval (.RightApplicationOfValue (.VLam (lambdaPrefix rest.length body) env) ::
        applicationFrames rest stack env) env first := by
  rw [stepN_add, stepN_applyParams]
  rfl

/-- Enter the first argument of two exactly saturated lambda spines. The
source forces the delayed body after the last argument, while the target
enters its related body directly. Arguments themselves can be arbitrary. -/
theorem eval_force_saturated_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R .same e e') (related : R .same lhs rhs)
    (refl : ∀ term, R .same term term) (first : Term) (rest : List Term) :
    ∃ n m, StateRel R
      (stepN variant (n + 1) (.Eval s e (.Force
        (applyParams (lambdaPrefix (rest.length + 1) (.Delay lhs)) (first :: rest)))))
      (stepN variant (m + 1) (.Eval t e'
        (applyParams (lambdaPrefix (rest.length + 1) rhs) (first :: rest)))) := by
  refine ⟨(first :: rest).length + 2, (first :: rest).length + 1, ?_⟩
  change StateRel R
    (stepN variant ((first :: rest).length + 2) (.Eval (.ForceFrame :: s) e
      (applyParams (lambdaPrefix (rest.length + 1) (.Delay lhs)) (first :: rest))))
    (stepN variant ((first :: rest).length + 2) (.Eval t e'
      (applyParams (lambdaPrefix (rest.length + 1) rhs) (first :: rest))))
  rw [enterSaturatedCall, enterSaturatedCall]
  exact .eval (.saturatedDelay rest stacks envs envs related) envs (refl first)

/-- Enter the shared condition before running either arm. Both right-hand
arms are immediate values, permitting the selected value to be returned
without the source's force and delay steps. -/
theorem eval_force_if_then_else_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R .same e e') (refl : ∀ term, R .same term term) (cond yes no : Term)
    (yesReady : immediateArm yes = true) (noReady : immediateArm no = true) :
    ∃ n m, StateRel R
      (stepN variant (n + 1) (.Eval s e (.Force (ifThenElseTerm cond (.Delay yes) (.Delay no)))))
      (stepN variant (m + 1) (.Eval t e' (ifThenElseTerm cond yes no))) :=
  ⟨7, 6, .eval (.delayedIf stacks envs yesReady noReady) envs (refl cond)⟩

theorem eval_var_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R layout e e') (idx : Nat) :
    StateRel R (step variant (.Eval s e (.Var idx)))
      (step variant (.Eval t e' (.Var (layout.rename idx)))) := by
  simp only [step, List.get?Internal_eq_getElem?]
  have related := envs.lookup idx
  generalize e[idx]? = left at related ⊢
  generalize e'[layout.rename idx]? = right at related ⊢
  cases related with
  | none => exact .error
  | some values => exact .ret stacks values

theorem eval_hoisted_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R layout e e') (selected : layout.hoistedAt index = some forced) :
    StateRel R (stepN variant (2 * forced.forces + 1) (.Eval s e forced.term))
      (step variant (.Eval t e' (.Var index))) := by
  rw [forced.evaluate]
  simp only [step, List.get?Internal_eq_getElem?, envs.hoistedLookup selected]
  exact .ret stacks (.builtin .nil)

theorem eval_constructor_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (envs : EnvRel R layout e e') (fields : TermListRel R layout xs ys) (tag : Nat) :
    StateRel R (step variant (.Eval s e (.Constr tag xs)))
      (step variant (.Eval t e' (.Constr tag ys))) := by
  cases fields with
  | nil => exact .ret stacks (.constr .nil)
  | cons terms rest =>
    exact .eval (.cons (.constructorArgument .nil rest envs) stacks) envs terms

end UplcOptimizer.Deep
