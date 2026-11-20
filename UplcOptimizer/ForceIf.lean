import UplcOptimizer.ContextualRules

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

private def forceIfResult : (term : Term) → Option { output : Term // TermRel term output }
  | .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) condition) (.Delay yes))
      (.Delay no)) =>
    if yesReady : immediateArm yes = true then
      if noReady : immediateArm no = true then
        some ⟨ifThenElseTerm condition yes no,
          .forceIfThenElse condition yes no yesReady noReady⟩
      else none
    else none
  | _ => none

def forceIfThenElse? (term : Term) : Option Term := (forceIfResult term).map Subtype.val

@[uplc_contextual_rule] theorem forceIfThenElse_sound : ContextualRule forceIfThenElse? :=
  .ofChecked forceIfResult

def_uplc_contextual_rules forceIfRule

end UplcOptimizer.Deep
