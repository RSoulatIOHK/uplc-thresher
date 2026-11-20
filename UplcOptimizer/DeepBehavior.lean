import UplcOptimizer.DeepCode
import UplcOptimizer.DeepMachine

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

private theorem ScopedTermsRel.toListRel (related : ScopedTermsRel layout lhs rhs) :
    TermListRel ScopedTermRel layout lhs rhs :=
  match related with
  | .nil => .nil
  | .cons head tail => .cons head tail.toListRel

private theorem step_prepared (ready : prepared t = true) (variant : BuiltinSemanticsVariant)
    (stack : Stack) (env : Environment) : step variant (.Eval stack env t) = prepare stack env t := by
  cases t <;> simp_all [prepared, prepare, step]

private def EvalProgress (variant : BuiltinSemanticsVariant) (layout : Layout)
    (lhs rhs : Term) : Prop :=
    ∀ (left right : Stack) (env env' : Environment), StackRel ScopedTermRel left right →
      EnvRel ScopedTermRel layout env env' →
      ∃ sourceSteps targetSteps, (prepared lhs = true → sourceSteps = 0) ∧
        StateRel ScopedTermRel (stepN variant (sourceSteps + 1) (.Eval left env lhs))
          (stepN variant (targetSteps + 1) (.Eval right env' rhs))

/-- Synchronize both machines after positive transition counts. A shared
    builtin can spend different amounts of time on either side, while a
    syntactic value on the source side takes exactly one step. -/
private theorem eval_progress (variant : BuiltinSemanticsVariant)
    (related : ScopedTermRel layout lhs rhs) : EvalProgress variant layout lhs rhs := by
  refine ScopedTermRel.rec (motive_1 := fun layout lhs rhs _ => EvalProgress variant layout lhs rhs)
    (motive_2 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trivial
    (fun _ _ _ _ => trivial) related
  · intro _ n _ _ _ _ stacks envs
    exact ⟨0, 0, fun _ => rfl, eval_var_related variant stacks envs n⟩
  · intro _ _ _ _ _ _ stacks _
    exact ⟨0, 0, fun _ => rfl, .ret stacks .const⟩
  · intro _ _ _ _ _ _ stacks _
    exact ⟨0, 0, fun _ => rfl, .ret stacks (.builtin .nil)⟩
  · intro _ _ _ _ _ _ _
    exact ⟨0, 0, fun _ => rfl, .error⟩
  · intro _ _ _ bodies _ _ _ _ _ stacks envs
    exact ⟨0, 0, fun _ => rfl, .ret stacks (.lam bodies envs)⟩
  · intro _ _ _ bodies _ _ _ _ _ stacks envs
    exact ⟨0, 0, fun _ => rfl, .ret stacks (.delay bodies envs)⟩
  · intro _ _ _ bodies _ _ _ _ _ stacks envs
    exact ⟨0, 0, fun _ => rfl, .eval (.cons .force stacks) envs bodies⟩
  · intro _ _ _ _ _ functions arguments _ _ _ _ _ _ stacks envs
    exact ⟨0, 0, fun _ => rfl, .eval (.cons (.leftTerm arguments envs) stacks) envs functions⟩
  · intro _ _ _ tag fields _ _ _ _ _ stacks envs
    exact ⟨0, 0, fun _ => rfl, eval_constructor_related variant stacks envs fields.toListRel tag⟩
  · intro _ _ _ _ _ scrutinees branches _ _ _ _ _ _ stacks envs
    exact ⟨0, 0, fun _ => rfl, .eval (.cons (.caseScrutinee branches.toListRel envs) stacks) envs scrutinees⟩
  · intro lhs mid _ _ rule _ ih left right env env' stacks envs
    obtain ⟨spent, entered⟩ := rule.advance variant left env
    obtain ⟨source, target, single, next⟩ := ih left right env env' stacks envs
    have impossible : prepared lhs ≠ true := by
      have active := rule.active
      cases lhs <;> simp_all [prepared, redex]
    cases ready : prepared mid with
    | false =>
      refine ⟨spent + 1 + source, target, fun h => (impossible h).elim, ?_⟩
      rw [Nat.add_assoc (spent + 1), stepN_add, entered, prepare_eval ready]
      exact next
    | true =>
      have zero := single ready
      subst source
      refine ⟨spent, target, fun h => (impossible h).elim, ?_⟩
      rw [entered]
      simpa only [stepN, step_prepared ready] using next
  · intro _ forced index found _ _ _ _ stacks envs
    refine ⟨2 * forced.forces, 0, ?_, ?_⟩
    · have notReady : prepared forced.term = false := by
        unfold ForcedBuiltin.term
        cases forced.forces <;> rfl
      simp [notReady]
    · exact eval_hoisted_related variant stacks envs found
  · intro _ _ body forced _ ih left right env env' stacks envs
    obtain ⟨source, target, single, next⟩ := ih left right env (forced.value :: env') stacks (.insert forced envs)
    refine ⟨source, (2 * forced.forces + 5) + target, single, ?_⟩
    rw [Nat.add_assoc, stepN_add variant (2 * forced.forces + 5) (target + 1), forced.enterLet]
    exact next

private theorem state_progress (variant : BuiltinSemanticsVariant)
    (related : StateRel ScopedTermRel lhs rhs) :
    ∃ left right, StateRel ScopedTermRel (stepN variant (left + 1) lhs)
      (stepN variant (right + 1) rhs) := by
  cases related with
  | eval stacks envs terms =>
    obtain ⟨left, right, _, next⟩ := eval_progress variant terms _ _ _ _ stacks envs
    exact ⟨left, right, next⟩
  | ret stacks values => exact ⟨0, 0, return_step_related variant stacks values⟩
  | halt values => exact ⟨0, 0, .halt values⟩
  | error => exact ⟨0, 0, .error⟩
  | budgetExhausted => exact ⟨0, 0, .budgetExhausted⟩

/-- Observable outcomes distinguish errors, successful termination with any
    value, and the literal constant returned by a successful computation. -/
inductive Observation
  | error
  | success
  | constant (value : Const)

def observed (state : State) (observation : Observation) : Prop :=
  match state, observation with
  | .Error, .error => True
  | .Halt _, .success => True
  | .Halt (.VCon found), .constant expected => found = expected
  | _, _ => False

private theorem StateRel.observed_iff (related : StateRel ScopedTermRel lhs rhs) (o : Observation) :
    observed lhs o ↔ observed rhs o := by
  cases related with
  | halt values => cases values <;> cases o <;> rfl
  | _ => cases o <;> rfl

private theorem observed_absorbing (h : observed state o) (variant : BuiltinSemanticsVariant)
    (count : Nat) : observed (stepN variant count state) o := by
  induction count generalizing state with
  | zero => exact h
  | succ count ih =>
    apply ih
    cases state <;> cases o <;> first | exact h | contradiction

private theorem transfer (variant : BuiltinSemanticsVariant) (result : Observation)
    {R : State → State → Prop}
    (agree : ∀ {a b}, R a b → (observed a result ↔ observed b result))
    (advance : ∀ {a b}, R a b → ∃ n m, R (stepN variant (n + 1) a) (stepN variant (m + 1) b))
    (steps : Nat) (related : R lhs rhs) (hit : observed (stepN variant steps lhs) result) :
    ∃ count, observed (stepN variant count rhs) result := by
  induction steps using Nat.strongRecOn generalizing lhs rhs with
  | ind steps ih =>
    obtain ⟨spent, other, next⟩ := advance related
    if available : spent + 1 ≤ steps then
      let suffix := steps - (spent + 1)
      have count : steps = (spent + 1) + suffix := by omega
      have rest : observed (stepN variant suffix (stepN variant (spent + 1) lhs)) result := by
        rw [← stepN_add, ← count]
        exact hit
      obtain ⟨count, reached⟩ := ih suffix (by omega) next rest
      exact ⟨other + 1 + count, by rw [stepN_add]; exact reached⟩
    else
      have count : spent + 1 = steps + (spent + 1 - steps) := by omega
      have oldHit : observed (stepN variant (spent + 1) lhs) result := by
        rw [count, stepN_add]
        exact observed_absorbing hit variant (spent + 1 - steps)
      exact ⟨other + 1, (agree next).mp oldHit⟩

/-- Each related run has exactly the same finite observations, with its own
    fuel. In particular, absence of both success and error is preserved. -/
theorem StateRel.observations (related : StateRel ScopedTermRel lhs rhs)
    (variant : BuiltinSemanticsVariant) (result : Observation) :
    (∃ steps, observed (stepN variant steps lhs) result) ↔
      (∃ steps, observed (stepN variant steps rhs) result) := by
  constructor
  · rintro ⟨count, reached⟩
    exact transfer variant result (fun r => r.observed_iff result) (state_progress variant)
      count related reached
  · rintro ⟨count, reached⟩
    refine transfer variant result (R := fun a b => StateRel ScopedTermRel b a)
      (fun r => (r.observed_iff result).symm) ?_ count related reached
    intro a b rel
    obtain ⟨n, m, next⟩ := state_progress variant rel
    exact ⟨m, n, next⟩

/-- A UPLC context with one hole, including positions under binders and
    suspended computations. Plugging uses the AST's de Bruijn indices. -/
inductive Context
  | hole
  | lam (body : Context)
  | delay (body : Context)
  | force (body : Context)
  | applyFn (fn : Context) (arg : Term)
  | applyArg (fn : Term) (arg : Context)
  | constrField (tag : Nat) (before : List Term) (field : Context) (after : List Term)
  | caseScrutinee (scrutinee : Context) (branches : List Term)
  | caseBranch (scrutinee : Term) (before : List Term) (branch : Context) (after : List Term)

def Context.plug (ctx : Context) (term : Term) : Term :=
  match ctx with
  | .hole => term
  | .lam body => .Lam (body.plug term)
  | .delay body => .Delay (body.plug term)
  | .force body => .Force (body.plug term)
  | .applyFn fn arg => .Apply (fn.plug term) arg
  | .applyArg fn arg => .Apply fn (arg.plug term)
  | .constrField tag before field after => .Constr tag (before ++ field.plug term :: after)
  | .caseScrutinee scrutinee branches => .Case (scrutinee.plug term) branches
  | .caseBranch scrutinee before branch after => .Case scrutinee (before ++ branch.plug term :: after)

private theorem TermsRel.surround (before after : List Term) (related : TermRel lhs rhs) :
    TermsRel (before ++ lhs :: after) (before ++ rhs :: after) := by
  induction before with
  | nil => exact .cons related (TermsRel.refl after)
  | cons first _ ih => exact .cons (TermRel.refl first) ih

theorem Context.related (ctx : Context) (related : TermRel lhs rhs) :
    TermRel (ctx.plug lhs) (ctx.plug rhs) := by
  induction ctx with
  | hole => exact related
  | lam _ h => exact .lam h
  | delay _ h => exact .delay h
  | force _ h => exact .force h
  | applyFn _ arg h => exact .apply h (TermRel.refl arg)
  | applyArg fn _ h => exact .apply (TermRel.refl fn) h
  | constrField tag before _ after h => exact .constr tag (TermsRel.surround before after h)
  | caseScrutinee _ branches h => exact .case h (TermsRel.refl branches)
  | caseBranch scrutinee before _ after h =>
    exact .case (TermRel.refl scrutinee) (TermsRel.surround before after h)

private theorem applyParams_related (args : List Term) (related : TermRel lhs rhs) :
    TermRel (applyParams lhs args) (applyParams rhs args) := by
  induction args generalizing lhs rhs with
  | nil => exact related
  | cons arg args ih => exact ih (.apply related (TermRel.refl arg))

private theorem observed_runSteps (variant : BuiltinSemanticsVariant) (fuel : Nat)
    (state : State) (o : Observation) :
    observed (runSteps variant state fuel) o ↔ observed (stepN variant fuel state) o := by
  induction fuel generalizing state with
  | zero => cases state <;> cases o <;> rfl
  | succ fuel ih =>
    cases state with
    | Eval | Return => exact ih _
    | Error => simpa only [stepN, step, runSteps] using ih State.Error
    | Halt value => simpa only [stepN, step, runSteps] using ih (State.Halt value)
    | BudgetExhausted => simpa only [stepN, step, runSteps] using ih State.BudgetExhausted

/-- Unmetered observations of the reference evaluator at some finite fuel.
    Exhaustion is distinct from a runtime error. -/
def Evaluates (variant : BuiltinSemanticsVariant) (p : Program) (args : List Term)
    (o : Observation) : Prop :=
  ∃ fuel, observed (cekExecuteProgramWithSemanticVariant variant p args fuel) o

/-- Contextual equivalence for the observations of the pinned CEK model.
    Higher-order results can be applied or forced by the observing context. -/
def ProgramEquivalent (source target : Program) : Prop :=
  match source, target with
  | .Program v body, .Program w result =>
    ∀ (ctx : Context) (variant : BuiltinSemanticsVariant) (args : List Term) (o : Observation),
      Evaluates variant (.Program v (ctx.plug body)) args o ↔
        Evaluates variant (.Program w (ctx.plug result)) args o

theorem TermRel.programEquivalent (related : TermRel lhs rhs) (version : Version) :
    ProgramEquivalent (.Program version lhs) (.Program version rhs) := by
  intro ctx variant args o
  have initial : StateRel ScopedTermRel (initialState (applyParams (ctx.plug lhs) args))
      (initialState (applyParams (ctx.plug rhs) args)) :=
    .eval .nil (.same .nil) (applyParams_related args (ctx.related related))
  have relatedObservations := initial.observations variant o
  simpa only [Evaluates, cekExecuteProgramWithSemanticVariant, observed_runSteps] using
    relatedObservations

theorem TermRel.Chain.programEquivalent (related : TermRel.Chain lhs rhs) (version : Version) :
    ProgramEquivalent (.Program version lhs) (.Program version rhs) := by
  induction related with
  | refl term =>
    intro ctx variant args o
    exact Iff.rfl
  | step first _ ih =>
    intro ctx variant args o
    exact (first.programEquivalent version ctx variant args o).trans (ih ctx variant args o)

end UplcOptimizer.Deep
