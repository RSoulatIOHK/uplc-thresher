import UplcOptimizer.DeepCode

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

structure SharedTerm (layout : Layout) (input : Term) where
  output : Term
  uses : Nat
  proof : ScopedTermRel layout input output

abbrev Substitute := (layout : Layout) → (term : Term) →
  Option { out : Term // ScopedTermRel layout term out }

mutual
  /-- Replace chosen uses and rename existing variables for the new layout. -/
  def rewriteShared (substitute : Substitute) (layout : Layout) (term : Term) :
      SharedTerm layout term :=
    if let some use := substitute layout term then
      ⟨use.val, 1, use.property⟩
    else
      match term with
      | .Var index => ⟨.Var (layout.rename index), 0, .var index⟩
      | .Const value => ⟨.Const value, 0, .const value⟩
      | .Builtin builtin => ⟨.Builtin builtin, 0, .builtin builtin⟩
      | .Error => ⟨.Error, 0, .error⟩
      | .Lam body =>
        let result := rewriteShared substitute layout.underBinder body
        ⟨.Lam result.output, result.uses, .lam result.proof⟩
      | .Delay body =>
        let result := rewriteShared substitute layout body
        ⟨.Delay result.output, result.uses, .delay result.proof⟩
      | .Force body =>
        let result := rewriteShared substitute layout body
        ⟨.Force result.output, result.uses, .force result.proof⟩
      | .Apply fn arg =>
        let fn := rewriteShared substitute layout fn
        let arg := rewriteShared substitute layout arg
        ⟨.Apply fn.output arg.output, fn.uses + arg.uses, .apply fn.proof arg.proof⟩
      | .Constr tag fields =>
        let result := rewriteSharedChildren substitute layout fields
        ⟨.Constr tag result.val.1, result.val.2, .constr tag result.property⟩
      | .Case scrutinee branches =>
        let result := rewriteShared substitute layout scrutinee
        let arms := rewriteSharedChildren substitute layout branches
        ⟨.Case result.output arms.val.1, result.uses + arms.val.2,
          .case result.proof arms.property⟩
  termination_by sizeOf term

  private def rewriteSharedChildren (substitute : Substitute) (layout : Layout) (terms : List Term) :
      { result : List Term × Nat // ScopedTermsRel layout terms result.1 } :=
    match terms with
    | [] => ⟨([], 0), .nil⟩
    | term :: rest =>
      let head := rewriteShared substitute layout term
      let tail := rewriteSharedChildren substitute layout rest
      ⟨(head.output :: tail.val.1, head.uses + tail.val.2), .cons head.proof tail.property⟩
  termination_by sizeOf terms
end

end UplcOptimizer.Deep
