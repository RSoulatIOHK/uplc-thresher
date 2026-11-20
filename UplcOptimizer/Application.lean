import UplcOptimizer.LocalProofs

namespace UplcOptimizer

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- The argument frames of a left-associated application, with the first
    argument closest to the function. -/
def applicationFrames (args : List Term) (stack : Stack) (env : Environment) : Stack :=
  args.foldr (fun arg rest => .LeftApplicationToTerm arg env :: rest) stack

theorem stepN_applyParams (variant : BuiltinSemanticsVariant) (args : List Term)
    (body : Term) (stack : Stack) (env : Environment) :
    stepN variant args.length (.Eval stack env (applyParams body args)) =
      .Eval (applicationFrames args stack env) env body := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    change stepN variant (args.length + 1) (.Eval stack env (applyParams (.Apply body arg) args)) = _
    rw [stepN_add, ih]
    rfl

/-- Wrap the body in `arity` consecutive lambda binders. -/
def lambdaPrefix : Nat → Term → Term
  | 0, body => body
  | arity + 1, body => .Lam (lambdaPrefix arity body)

end UplcOptimizer
