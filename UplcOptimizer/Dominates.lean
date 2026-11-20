import UplcOptimizer.CacheExpr
import UplcOptimizer.ForcedBuiltin

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- The needle is reached before any other computation that could fail or
diverge. All frames passed on this path leave the environment intact. -/
inductive FirstUse (needle : Term) : Term → Prop where
  | self : FirstUse needle needle
  | force : FirstUse needle body → FirstUse needle (.Force body)
  | applyFn : FirstUse needle fn → FirstUse needle (.Apply fn arg)
  | caseScrutinee : FirstUse needle scrutinee → FirstUse needle (.Case scrutinee branches)
  | constrFirst : FirstUse needle arg → FirstUse needle (.Constr tag (arg :: rest))
  | builtinArg : FirstUse needle arg → FirstUse needle (.Apply (.Builtin builtin) arg)
  | lambdaArg : FirstUse needle arg → FirstUse needle (.Apply (.Lam body) arg)
  | forcedArg (forced : ForcedBuiltin) : FirstUse needle arg →
      FirstUse needle (.Apply forced.term arg)

private theorem FirstUse.enter (witness : FirstUse needle lhs) (variant : BuiltinSemanticsVariant)
    (stack : Stack) (env : Environment) :
    ∃ count continuation, stepN variant count (.Eval stack env lhs) =
      .Eval continuation env needle := by
  induction witness generalizing stack with
  | self => exact ⟨0, stack, rfl⟩
  | force _ ih =>
    obtain ⟨count, continuation, entered⟩ := ih (.ForceFrame :: stack)
    exact ⟨count + 1, continuation, entered⟩
  | @applyFn fn arg _ ih =>
    obtain ⟨count, continuation, entered⟩ := ih (.LeftApplicationToTerm arg env :: stack)
    exact ⟨count + 1, continuation, entered⟩
  | @caseScrutinee scrutinee branches _ ih =>
    obtain ⟨count, continuation, entered⟩ := ih (.CaseScrutinee branches env :: stack)
    exact ⟨count + 1, continuation, entered⟩
  | @constrFirst arg tag rest _ ih =>
    obtain ⟨count, continuation, entered⟩ := ih (.ConstructorArgument tag [] rest env :: stack)
    exact ⟨count + 1, continuation, entered⟩
  | @builtinArg arg builtin _ ih =>
    obtain ⟨count, continuation, entered⟩ := ih
      (.RightApplicationOfValue (.VBuiltin builtin [] (PlutusCore.UPLC.Builtins.expectedArgs builtin)) :: stack)
    exact ⟨count + 3, continuation, entered⟩
  | @lambdaArg arg body _ ih =>
    obtain ⟨count, continuation, entered⟩ := ih (.RightApplicationOfValue (.VLam body env) :: stack)
    exact ⟨count + 3, continuation, entered⟩
  | @forcedArg arg forced _ ih =>
    obtain ⟨count, continuation, entered⟩ := ih (.RightApplicationOfValue forced.value :: stack)
    refine ⟨2 * forced.forces + 3 + count, continuation, ?_⟩
    rw [stepN_add variant (2 * forced.forces + 3)]
    rw [show 2 * forced.forces + 3 = (2 * forced.forces + 1) + 2 by omega]
    change stepN variant count (stepN variant ((2 * forced.forces + 1) + 1)
      (.Eval (.LeftApplicationToTerm arg env :: stack) env forced.term)) = _
    rw [stepN_add, forced.evaluate]
    exact entered

theorem FirstUse.error {expr : CacheExpr} (witness : FirstUse expr.term lhs)
    (failed : expr.eval env = none)
    (variant : BuiltinSemanticsVariant) (stack : Stack) :
    ∃ count, stepN variant (count + 1) (.Eval stack env lhs) = .Error := by
  obtain ⟨count, continuation, entered⟩ := witness.enter variant stack env
  have steps := expr.steps_pos
  refine ⟨count + expr.steps - 1, ?_⟩
  rw [show count + expr.steps - 1 + 1 = count + expr.steps by omega, stepN_add, entered,
    expr.run, failed]

end UplcOptimizer.Deep
