import UplcOptimizer.ContextualRules
import UplcOptimizer.Sharing
import PlutusCore.UPLC.Term.Instances

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

private structure Candidate (term : Term) where
  expr : CacheExpr
  first : FirstUse expr.term term

private def atRoot (term : Term) : List (Candidate term) :=
  match CacheExpr.match? term with
  | some ⟨.project op arg, equal⟩ =>
    [⟨.project op arg, equal ▸ FirstUse.self⟩]
  | _ => []

private def liftCandidates {inner outer : Term}
    (lift : ∀ {needle}, FirstUse needle inner → FirstUse needle outer)
    (candidates : List (Candidate inner)) : List (Candidate outer) :=
  candidates.map fun candidate => ⟨candidate.expr, lift candidate.first⟩

/-- Follow the initial evaluation path and consider larger projections first. -/
private def firstCandidates (term : Term) : List (Candidate term) :=
  atRoot term ++ match term with
    | .Force body => liftCandidates .force (firstCandidates body)
    | .Case scrutinee _ => liftCandidates .caseScrutinee (firstCandidates scrutinee)
    | .Constr _ (first :: _) => liftCandidates .constrFirst (firstCandidates first)
    | .Apply fn arg =>
      match fn with
      | .Lam _ => liftCandidates .lambdaArg (firstCandidates arg)
      | .Builtin _ => liftCandidates .builtinArg (firstCandidates arg)
      | fn =>
        match ForcedBuiltin.match? fn with
        | some ⟨forced, equal⟩ => liftCandidates
            (fun witness => equal.symm ▸ FirstUse.forcedArg forced witness) (firstCandidates arg)
        | none => liftCandidates .applyFn (firstCandidates fn)
    | _ => []
termination_by sizeOf term

-- This traversal introduces exactly one cache, and the layout keeps track of
-- where that entry appears under the original term's binders.
private def cacheIndex? : Layout → Option Nat
  | .same => none
  | .keep tail | .insert _ tail => (cacheIndex? tail).map Nat.succ
  | .cache .. => some 0

private def cachedSubstitution (layout : Layout) (term : Term) :
    Option { out : Term // ScopedTermRel layout term out } := do
  let index ← cacheIndex? layout
  match found : layout.cachedAt index with
  | none => none
  | some expr =>
    if equal : expr.term = term then
      some ⟨.Var index, equal ▸ .cachedReference expr index found⟩
    else none

private def cseResult (term : Term) : Option { output : Term // TermRel term output } := do
  if active : prepared term = false then
    (firstCandidates term).findSome? fun candidate =>
      let body := rewriteShared cachedSubstitution (.cache candidate.expr .same) term
      if body.uses ≥ 2 then
        some ⟨.Apply (.Lam body.output) candidate.expr.term,
          .shareCommonProjection candidate.expr candidate.first active body.proof⟩
      else none
  else none

def shareCommonProjection? (term : Term) : Option Term := (cseResult term).map Subtype.val

@[uplc_contextual_rule] theorem shareCommonProjection_sound : ContextualRule shareCommonProjection? :=
  .ofChecked cseResult

def_uplc_contextual_rules cseRule

end UplcOptimizer.Deep
