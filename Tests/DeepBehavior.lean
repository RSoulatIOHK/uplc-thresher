import UplcOptimizer

namespace Tests.DeepBehavior

open UplcOptimizer UplcOptimizer.Deep PlutusCore.Default PlutusCore.UPLC.Term

private def version : Version := .Version 1 1 0

private def bodyOf : Program → Term
  | .Program _ body => body

private def input : Program := .Program version (.Lam (.Force (.Delay (.Var 0))))

private def checked := optimizeWithProof input

#guard bodyOf checked.val.1 == .Lam (.Var 0)
#guard checked.val.2.rewrites == 1

example : ProgramEquivalent input checked.val.1 := checked.property

example (ctx : Context) (variant : BuiltinSemanticsVariant) (args : List Term) (result : Observation) :
    Evaluates variant (.Program version (ctx.plug (bodyOf input))) args result ↔
      Evaluates variant (.Program version (ctx.plug (bodyOf (optimize input).1))) args result :=
  optimize_preserves input 12 ctx variant args result

/-- info: 'UplcOptimizer.optimize_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UplcOptimizer.optimize_preserves

@[uplc_deep_rule] theorem forceTwoDelays (body : Term) :
    StepRule (.Force (.Force (.Delay (.Delay body)))) body := by
  constructor
  · rfl
  · intro variant stack env
    cases body <;> first | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩

def_uplc_deep_rules extendedRules

private def wrapped : Term := .Force (.Force (.Delay (.Delay (.Var 0))))

#guard (UplcOptimizer.Deep.rootRule wrapped).isNone
#guard (extendedRules wrapped).map Subtype.val == some (.Var 0)
#guard (optimizeTerm extendedRules (.Lam wrapped) 1).val.1 == .Lam (.Var 0)

example : TermRel.Chain (.Lam wrapped) (optimizeTerm extendedRules (.Lam wrapped) 1).val.1 :=
  (optimizeTerm extendedRules (.Lam wrapped) 1).property

end Tests.DeepBehavior
