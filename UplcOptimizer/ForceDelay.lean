import UplcOptimizer.ContextualRules

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term

private def checkedSaturatedDelay (input : Term) :
    Option { output : Term // TermRel (.Force input) output } := do
  let ⟨(fn, args), source⟩ := applicationSpine input []
  match args with
  | [] => none
  | first :: rest => do
    let ⟨.Delay body, lambdaShape⟩ ← lambdaBody? (rest.length + 1) fn | none
    let output := applyParams (lambdaPrefix (rest.length + 1) body) (first :: rest)
    return ⟨output, by
      change applyParams fn (first :: rest) = input at source
      rw [← source, lambdaShape]
      exact .forceDelaySaturated first rest (TermRel.refl body)⟩

private def forceDelayResult : (term : Term) → Option { output : Term // TermRel term output }
  | .Force (.Apply fn arg) => checkedSaturatedDelay (.Apply fn arg)
  | _ => none

def forceDelaySaturated? (term : Term) : Option Term := (forceDelayResult term).map Subtype.val

@[uplc_contextual_rule] theorem forceDelaySaturated_sound : ContextualRule forceDelaySaturated? :=
  .ofChecked forceDelayResult

def_uplc_contextual_rules forceDelayRule

end UplcOptimizer.Deep
