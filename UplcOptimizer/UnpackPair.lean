import UplcOptimizer.ContextualRules
import UplcOptimizer.Sharing

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

private def substituteField (layout : Layout) (index : Nat) (first : Bool) :
    Option { output : Term // ScopedTermRel layout (pairProjection index first) output } :=
  match found : layout.pairField index first with
  | none => none
  | some slot => some ⟨.Var slot, .splitPairProjection index first slot found⟩

private def pairSubstitution : Substitute := fun layout term =>
  match term with
  | .Case (.Var index) [.Lam (.Lam (.Var 1))] => substituteField layout index true
  | .Case (.Var index) [.Lam (.Lam (.Var 0))] => substituteField layout index false
  | _ => none

/-- Destructure the successful result of a strict `unConstrData` binding once.
    The traversal rejects any use of the old pair outside a recognized projection. -/
private def unpackPairResult : (term : Term) → Option { output : Term // TermRel term output }
  | .Apply (.Lam body) (.Apply (.Builtin .UnConstrData) arg) => do
    let rewritten ← rewriteShared? pairSubstitution (.splitPair .same) body
    if rewritten.uses ≥ 2 then
      some ⟨.Case (unConstrDataTerm arg) [.Lam (.Lam rewritten.output)],
        .unpackPairLet arg rewritten.proof⟩
    else none
  | _ => none

def unpackPairLet? (term : Term) : Option Term := (unpackPairResult term).map Subtype.val

@[uplc_contextual_rule] theorem unpackPairLet_sound : ContextualRule unpackPairLet? :=
  .ofChecked unpackPairResult

def_uplc_contextual_rules unpackPairRule

end UplcOptimizer.Deep
