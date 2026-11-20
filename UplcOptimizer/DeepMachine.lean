import UplcOptimizer.DeepValues
import PlutusCore.UPLC.CekMachine

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

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

abbrev StackRel (R : Layout → Term → Term → Prop) := ListRel (FrameRel R)

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

/-- A return transition preserves structurally related stacks and values. -/
theorem return_step_related (variant : BuiltinSemanticsVariant) (stacks : StackRel R s t)
    (values : ValueRel R v w) :
    StateRel R (step variant (.Return s v)) (step variant (.Return t w)) := by
  cases stacks with
  | nil => exact .halt values
  | cons frames stacks =>
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
