import UplcOptimizer.DeepCode
import UplcOptimizer.DeepMachine

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

private theorem TermsRel.toListRel (related : TermsRel lhs rhs) : TermListRel TermRel lhs rhs :=
  match related with
  | .nil => .nil
  | .cons head tail => .cons head tail.toListRel

private theorem prepared_related (variant : BuiltinSemanticsVariant)
    (stacks : StackRel TermRel left right) (envs : ValueListRel TermRel env env')
    (terms : TermRel lhs rhs) (ready : prepared lhs = true) :
    StateRel TermRel (prepare left env lhs) (step variant (.Eval right env' rhs)) := by
  cases terms with
  | const => exact .ret stacks .const
  | lam bodies => exact .ret stacks (.lam bodies envs)
  | delay bodies => exact .ret stacks (.delay bodies envs)
  | error => exact .error
  | reduce reduction _ =>
    have active := reduction.active
    cases lhs <;> simp_all [redex, prepared]
  | var | builtin | force | apply | constr | case => simp [prepared] at ready

/-- A single optimized CEK transition accounts for a positive number of
    original transitions. Related environments and frames account for
    retained code that will be evaluated later. -/
private theorem eval_progress (variant : BuiltinSemanticsVariant) (related : TermRel lhs rhs) :
    ∀ {left right env env'}, StackRel TermRel left right → ValueListRel TermRel env env' →
      ∃ count, StateRel TermRel (stepN variant (count + 1) (.Eval left env lhs))
        (step variant (.Eval right env' rhs)) := by
  intro left right env env'
  refine TermRel.rec (motive_2 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ trivial
    (fun _ _ _ _ => trivial) related
  · intro n stacks envs
    exact ⟨0, eval_var_related variant stacks envs n⟩
  · intro _ stacks _
    exact ⟨0, .ret stacks .const⟩
  · intro _ stacks _
    exact ⟨0, .ret stacks (.builtin .nil)⟩
  · intro _ _
    exact ⟨0, .error⟩
  · intro _ _ bodies _ stacks envs
    exact ⟨0, .ret stacks (.lam bodies envs)⟩
  · intro _ _ bodies _ stacks envs
    exact ⟨0, .ret stacks (.delay bodies envs)⟩
  · intro _ _ bodies _ stacks envs
    exact ⟨0, .eval (.cons .force stacks) envs bodies⟩
  · intro _ _ _ _ functions arguments _ _ stacks envs
    exact ⟨0, .eval (.cons (.leftTerm arguments envs) stacks) envs functions⟩
  · intro _ _ tag fields _ stacks envs
    exact ⟨0, eval_constructor_related variant stacks envs fields.toListRel tag⟩
  · intro _ _ _ _ scrutinees branches _ _ stacks envs
    exact ⟨0, .eval (.cons (.caseScrutinee branches.toListRel envs) stacks) envs scrutinees⟩
  · intro _ mid _ rule tail ih stacks envs
    obtain ⟨count, head⟩ := rule.advance variant left env
    cases ready : prepared mid with
    | false =>
      obtain ⟨steps, next⟩ := ih stacks envs
      have join := prepare_eval ready left env
      refine ⟨count + 1 + steps, ?_⟩
      rw [Nat.add_assoc (count + 1), stepN_add, head, join]
      exact next
    | true =>
      refine ⟨count, ?_⟩
      rw [head]
      exact prepared_related variant stacks envs tail ready

private theorem state_progress (variant : BuiltinSemanticsVariant) (related : StateRel TermRel lhs rhs) :
    ∃ count, StateRel TermRel (stepN variant (count + 1) lhs) (step variant rhs) := by
  cases related with
  | eval stacks envs terms => exact eval_progress variant terms stacks envs
  | ret stacks values => exact ⟨0, return_step_related variant stacks values⟩
  | halt values => exact ⟨0, .halt values⟩
  | error => exact ⟨0, .error⟩
  | budgetExhausted => exact ⟨0, .budgetExhausted⟩

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

private theorem StateRel.observed_iff (related : StateRel TermRel lhs rhs) (o : Observation) :
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

private theorem transferRight (variant : BuiltinSemanticsVariant) (steps : Nat)
    (related : StateRel TermRel lhs rhs) (result : Observation)
    (hit : observed (stepN variant steps rhs) result) :
    ∃ count, observed (stepN variant count lhs) result := by
  induction steps generalizing lhs rhs with
  | zero =>
    exact ⟨0, (related.observed_iff result).mpr hit⟩
  | succ steps ih =>
    obtain ⟨spent, next⟩ := state_progress variant related
    obtain ⟨suffix, observedAfter⟩ := ih next hit
    exact ⟨(spent + 1) + suffix, by rw [stepN_add]; exact observedAfter⟩

private theorem transferLeft (variant : BuiltinSemanticsVariant) (steps : Nat)
    (related : StateRel TermRel lhs rhs) (result : Observation)
    (hit : observed (stepN variant steps lhs) result) :
    ∃ count, observed (stepN variant count rhs) result := by
  induction steps using Nat.strongRecOn generalizing lhs rhs with
  | ind steps ih =>
    obtain ⟨spent, next⟩ := state_progress variant related
    if available : spent + 1 ≤ steps then
      let suffix := steps - (spent + 1)
      have count : steps = (spent + 1) + suffix := by omega
      have rest : observed (stepN variant suffix (stepN variant (spent + 1) lhs)) result := by
        rw [← stepN_add, ← count]
        exact hit
      obtain ⟨count, reached⟩ := ih suffix (by omega) next rest
      exact ⟨count + 1, reached⟩
    else
      have count : spent + 1 = steps + (spent + 1 - steps) := by omega
      have oldHit : observed (stepN variant (spent + 1) lhs) result := by
        rw [count, stepN_add]
        exact observed_absorbing hit variant (spent + 1 - steps)
      exact ⟨1, (next.observed_iff result).mp oldHit⟩

/-- Each related run has exactly the same finite observations, with its own
    fuel. In particular, absence of both success and error is preserved. -/
theorem StateRel.observations (related : StateRel TermRel lhs rhs)
    (variant : BuiltinSemanticsVariant) (result : Observation) :
    (∃ steps, observed (stepN variant steps lhs) result) ↔
      (∃ steps, observed (stepN variant steps rhs) result) :=
  ⟨fun ⟨steps, hit⟩ => transferLeft variant steps related result hit,
    fun ⟨steps, hit⟩ => transferRight variant steps related result hit⟩


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
  | nil => exact .cons related (.refl after)
  | cons first _ ih => exact .cons (.refl first) ih

theorem Context.related (ctx : Context) (related : TermRel lhs rhs) :
    TermRel (ctx.plug lhs) (ctx.plug rhs) := by
  induction ctx with
  | hole => exact related
  | lam _ h => exact .lam h
  | delay _ h => exact .delay h
  | force _ h => exact .force h
  | applyFn _ arg h => exact .apply h (.refl arg)
  | applyArg fn _ h => exact .apply (.refl fn) h
  | constrField tag before _ after h => exact .constr tag (TermsRel.surround before after h)
  | caseScrutinee _ branches h => exact .case h (.refl branches)
  | caseBranch scrutinee before _ after h =>
    exact .case (.refl scrutinee) (TermsRel.surround before after h)

private theorem applyParams_related (args : List Term) (related : TermRel lhs rhs) :
    TermRel (applyParams lhs args) (applyParams rhs args) := by
  induction args generalizing lhs rhs with
  | nil => exact related
  | cons arg args ih => exact ih (.apply related (.refl arg))

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
  have initial : StateRel TermRel (initialState (applyParams (ctx.plug lhs) args))
      (initialState (applyParams (ctx.plug rhs) args)) :=
    .eval .nil .nil (applyParams_related args (ctx.related related))
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
