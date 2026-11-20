import UplcOptimizer.ContextualRules

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

/-- A matcher returning the replacement and its checked root rewrite. -/
abbrev RuleDispatch := (term : Term) → Option { result : Term // StepRule term result }

structure DeepStats where
  rewrites : Nat := 0
  sweeps : Nat := 0
  contextualRules : List String := []
  deriving Inhabited

private structure RewriteCounts where
  localSteps : Nat := 0
  contextualRules : List String := []

private def RewriteCounts.add (a b : RewriteCounts) : RewriteCounts :=
  ⟨a.localSteps + b.localSteps, a.contextualRules ++ b.contextualRules⟩

private def RewriteCounts.total (counts : RewriteCounts) : Nat :=
  counts.localSteps + counts.contextualRules.length

private abbrev SweepResult (before : Term) :=
  { result : Term × RewriteCounts // TermRel before result.1 }

private abbrev HeadResult (before : Term) :=
  { result : Term × Nat // ∀ after, TermRel result.1 after → TermRel before after }

/-- A head contraction can be prepended to any subsequent structural proof. -/
private def contractHead (rewrite : RuleDispatch) :
    (fuel : Nat) → (term : Term) → HeadResult term
  | 0, term => ⟨(term, 0), fun _ related => related⟩
  | fuel + 1, term =>
    match rewrite term with
    | none => ⟨(term, 0), fun _ related => related⟩
    | some first =>
      let rest := contractHead rewrite fuel first.val
      ⟨(rest.val.1, rest.val.2 + 1), fun after related =>
        .reduce first.property (rest.property after related)⟩

private def walkTerms (walk : (term : Term) → SweepResult term) :
    (terms : List Term) → { result : List Term × RewriteCounts // TermsRel terms result.1 }
  | [] => ⟨([], {}), .nil⟩
  | term :: terms =>
    let first := walk term
    let rest := walkTerms walk terms
    ⟨(first.val.1 :: rest.val.1, first.val.2.add rest.val.2),
      .cons first.property rest.property⟩

private def walkChildren (walk : (term : Term) → SweepResult term) :
    (term : Term) → SweepResult term
  | .Lam body =>
    let body := walk body
    ⟨(.Lam body.val.1, body.val.2), .lam body.property⟩
  | .Delay body =>
    let body := walk body
    ⟨(.Delay body.val.1, body.val.2), .delay body.property⟩
  | .Force body =>
    let body := walk body
    ⟨(.Force body.val.1, body.val.2), .force body.property⟩
  | .Apply fn argument =>
    let fn := walk fn
    let argument := walk argument
    ⟨(.Apply fn.val.1 argument.val.1, fn.val.2.add argument.val.2),
      .apply fn.property argument.property⟩
  | .Constr tag fields =>
    let fields := walkTerms walk fields
    ⟨(.Constr tag fields.val.1, fields.val.2), .constr tag fields.property⟩
  | .Case scrutinee branches =>
    let scrutinee := walk scrutinee
    let branches := walkTerms walk branches
    ⟨(.Case scrutinee.val.1 branches.val.1, scrutinee.val.2.add branches.val.2),
      .case scrutinee.property branches.property⟩
  | term => ⟨(term, {}), TermRel.refl term⟩

-- Contractions may introduce deeper syntax. A subsequent sweep visits any
-- new descendants that exceed the current sweep's input height.
private def sweep (rewrite : RuleDispatch) (contextual : ContextualDispatch) :
    (depth : Nat) → (term : Term) → SweepResult term
  | 0, term => ⟨(term, {}), TermRel.refl term⟩
  | depth + 1, term =>
    let head := contractHead rewrite 16 term
    match contextual head.val.1 with
    | some rule =>
      ⟨(rule.output, ⟨head.val.2, [rule.theoremName]⟩), head.property _ rule.proof⟩
    | none =>
      let children := walkChildren (sweep rewrite contextual depth) head.val.1
      let counts := { children.val.2 with localSteps := head.val.2 + children.val.2.localSteps }
      ⟨(children.val.1, counts), head.property _ children.property⟩

mutual
  private def termDepth : Term → Nat
    | .Lam body | .Delay body | .Force body => 1 + termDepth body
    | .Apply fn argument => 1 + max (termDepth fn) (termDepth argument)
    | .Constr _ fields => 1 + termsDepth fields
    | .Case scrutinee branches => 1 + max (termDepth scrutinee) (termsDepth branches)
    | _ => 1
  termination_by term => sizeOf term
  decreasing_by all_goals simp_wf <;> omega

  private def termsDepth : List Term → Nat
    | [] => 0
    | term :: terms => max (termDepth term) (termsDepth terms)
  termination_by terms => sizeOf terms
  decreasing_by all_goals simp_wf <;> omega
end

private def optimizeTermWithFuel (rewrite : RuleDispatch) (contextual : ContextualDispatch)
    (late : Option ContextualDispatch) :
    (fuel : Nat) → (term : Term) → { result : Term × DeepStats // TermRel.Chain term result.1 }
  | 0, term => ⟨(term, {}), .refl term⟩
  | fuel + 1, term =>
    let depth := termDepth term
    let early := sweep rewrite contextual depth term
    -- Give local simplifications, including selection on a known condition,
    -- priority over a contextual rewrite that changes the branch shape.
    let first := match late with
      | some dispatch =>
        if early.val.2.total == 0 then sweep (fun _ => none) dispatch depth term else early
      | none => early
    let counts := first.val.2
    let rewrites := counts.total
    if rewrites == 0 then
      ⟨(term, { sweeps := 1 }), .refl term⟩
    else
      let rest := optimizeTermWithFuel rewrite contextual late fuel first.val.1
      let stats : DeepStats :=
        { rewrites := rewrites + rest.val.2.rewrites
          sweeps := 1 + rest.val.2.sweeps
          contextualRules := counts.contextualRules ++ rest.val.2.contextualRules }
      ⟨(rest.val.1, stats), .step first.property rest.property⟩

/-- Traverse the term and repeat until no rule fires or the sweep limit is reached. -/
def optimizeTerm (rewrite : RuleDispatch) (term : Term) (maxSweeps : Nat := 12)
    (contextual : ContextualDispatch := fun _ => none) (late : Option ContextualDispatch := none) :
    { result : Term × DeepStats // TermRel.Chain term result.1 } :=
  optimizeTermWithFuel rewrite contextual late maxSweeps term

end UplcOptimizer.Deep
