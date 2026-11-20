import UplcOptimizer.ContextualRules

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.Term

/-- Peel a left-associated application into its function and arguments. -/
private def applicationSpine (term : Term) (args : List Term) :
    { spine : Term × List Term // applyParams spine.1 spine.2 = applyParams term args } :=
  match term with
  | .Apply fn arg => applicationSpine fn (arg :: args)
  | term => ⟨(term, args), rfl⟩

/-- Accept exactly the requested number of lambdas followed by a delay. -/
private def delayedBody? : (arity : Nat) → (term : Term) →
    Option { body : Term // term = lambdaPrefix arity (.Delay body) }
  | 0, .Delay body => some ⟨body, rfl⟩
  | arity + 1, .Lam term => (delayedBody? arity term).map fun found =>
      ⟨found.val, congrArg Term.Lam found.property⟩
  | _, _ => none

private def checkedSaturatedDelay (input : Term) :
    Option { output : Term // TermRel (.Force input) output } := do
  let ⟨(fn, args), source⟩ := applicationSpine input []
  match args with
  | [] => none
  | first :: rest => do
    let ⟨body, lambdaShape⟩ ← delayedBody? (rest.length + 1) fn
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
