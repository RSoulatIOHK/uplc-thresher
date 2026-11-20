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

/-- Peel a left-associated application into its function and ordered arguments. -/
def applicationSpine (term : Term) (args : List Term := []) :
    { spine : Term × List Term // applyParams spine.1 spine.2 = applyParams term args } :=
  match term with
  | .Apply fn arg => applicationSpine fn (arg :: args)
  | term => ⟨(term, args), rfl⟩

/-- Remove a known number of lambda binders, retaining their exact shape in
    the witness. The remaining body may itself be a lambda. -/
def lambdaBody? : (arity : Nat) → (term : Term) →
    Option { body : Term // term = lambdaPrefix arity body }
  | 0, term => some ⟨term, rfl⟩
  | arity + 1, .Lam body => (lambdaBody? arity body).map fun found =>
      ⟨found.val, congrArg Term.Lam found.property⟩
  | _, _ => none

end UplcOptimizer
