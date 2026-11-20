import UplcOptimizer.ContextualRules

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term

private def checkedLambdaPacking (term : Term) :
    Option { output : Term // TermRel term output } := do
  let ⟨(fn, args), source⟩ := applicationSpine term
  match args with
  | first :: second :: third :: rest => do
    let tail := second :: third :: rest
    let ⟨body, lambdaShape⟩ ← lambdaBody? (tail.length + 1) fn
    return ⟨.Case (.Constr 0 (first :: tail)) [fn], by
      change applyParams fn (first :: tail) = term at source
      rw [← source, lambdaShape]
      exact .packLambdaApplications first tail (TermRel.refl body)⟩
  | _ => none

private def packLambdaResult : (term : Term) → Option { output : Term // TermRel term output }
  | .Apply (.Apply (.Apply fn first) second) third =>
    checkedLambdaPacking (.Apply (.Apply (.Apply fn first) second) third)
  | _ => none

private def packConditionalResult : (term : Term) → Option { output : Term // TermRel term output }
  | .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) condition) yes) no =>
    if yesReady : immediateArm yes = true then
      if noReady : immediateArm no = true then
        some ⟨.Case (.Constr 0 [condition, yes, no]) [.Force (.Builtin .IfThenElse)],
          .packConditionalApplications condition yes no yesReady noReady⟩
      else none
    else none
  | _ => none

def packLambdaApplications? (term : Term) : Option Term := (packLambdaResult term).map Subtype.val

def packConditionalApplications? (term : Term) : Option Term :=
  (packConditionalResult term).map Subtype.val

@[uplc_contextual_rule] theorem packLambdaApplications_sound : ContextualRule packLambdaApplications? :=
  .ofChecked packLambdaResult

@[uplc_contextual_rule] theorem packConditionalApplications_sound :
    ContextualRule packConditionalApplications? :=
  .ofChecked packConditionalResult

def_uplc_contextual_rules packingRules

/-- Only UPLC 1.1 and later can represent the packed term. -/
def supportsCasePacking : Version → Bool
  | .Version major minor _ => decide (major > 1 ∨ (major = 1 ∧ minor ≥ 1))

def applyToCaseRule (version : Version) : ContextualDispatch :=
  if supportsCasePacking version then packingRules else fun _ => none

end UplcOptimizer.Deep
