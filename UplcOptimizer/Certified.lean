import UplcOptimizer.LocalProofs

namespace UplcOptimizer

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

def_uplc_rules rootRule

/-- Apply a proof-producing root dispatcher at most `fuel` times. The second
result records the number of rewrites performed. -/
def certifiedRootWith (rewrite : (term : Term) → Option { result : Term // CekJoin term result }) :
    (fuel : Nat) → (term : Term) → { result : Term × Nat // CekJoin term result.1 }
  | 0, term => ⟨(term, 0), CekJoin.refl term⟩
  | fuel + 1, term =>
    match rewrite term with
    | none => ⟨(term, 0), CekJoin.refl term⟩
    | some first =>
      let rest := certifiedRootWith rewrite fuel first.1
      ⟨(rest.1.1, rest.1.2 + 1), first.2.trans rest.2⟩

/-- Apply the rules generated from the standard tagged theorems. -/
def certifiedRoot := certifiedRootWith rootRule

private def applicationFrames (args : List Term) (stack : Stack) (env : Environment) : Stack :=
  args.foldr (fun arg rest => .LeftApplicationToTerm arg env :: rest) stack

private theorem stepN_applyParams (variant : BuiltinSemanticsVariant) (args : List Term)
    (body : Term) (stack : Stack) (env : Environment) :
    stepN variant args.length (.Eval stack env (applyParams body args)) =
      .Eval (applicationFrames args stack env) env body := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    change stepN variant (args.length + 1) (.Eval stack env (applyParams (.Apply body arg) args)) = _
    rw [stepN_add, ih]
    rfl

/-- Applying the same explicit arguments preserves a root CEK join. They are
placed on the continuation before either function term begins evaluation. -/
theorem CekJoin.applyParams {lhs rhs : Term} (joined : CekJoin lhs rhs) (args : List Term) :
    CekJoin (PlutusCore.UPLC.CekMachine.applyParams lhs args)
      (PlutusCore.UPLC.CekMachine.applyParams rhs args) := by
  intro variant stack env
  obtain ⟨leftSteps, rightSteps, same⟩ := joined variant (applicationFrames args stack env) env
  refine ⟨args.length + leftSteps, args.length + rightSteps, ?_⟩
  simpa only [stepN_add, stepN_applyParams] using same

/-- Wrap the body in `arity` consecutive lambda binders. -/
def lambdaPrefix : Nat → Term → Term
  | 0, body => body
  | arity + 1, body => .Lam (lambdaPrefix arity body)

private theorem stepN_literalPrefix (variant : BuiltinSemanticsVariant) (args : List Const)
    (body : Term) (stack : Stack) (caller captured : Environment) :
    stepN variant (args.length * 4)
      (.Eval (applicationFrames (args.map .Const) stack caller) captured
        (lambdaPrefix args.length body)) =
      .Eval stack (args.foldl (fun env c => .VCon c :: env) captured) body := by
  induction args generalizing captured with
  | nil => rfl
  | cons arg args ih =>
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm _ 4, stepN_add]
    exact ih (.VCon arg :: captured)

private theorem enterLiteralPrefix (variant : BuiltinSemanticsVariant) (args : List Const)
    (body : Term) (stack : Stack) (env : Environment) :
    stepN variant ((args.map Term.Const).length + args.length * 4)
      (.Eval stack env (applyParams (lambdaPrefix args.length body) (args.map .Const))) =
      .Eval stack (args.foldl (fun env c => .VCon c :: env) env) body := by
  rw [stepN_add, stepN_applyParams, stepN_literalPrefix]

/-- A body join is preserved when exactly the enclosing lambda arity of
literal constant arguments is supplied. This is an applied-program theorem. -/
theorem certifiedLiteralPrefix {lhs rhs : Term} (joined : CekJoin lhs rhs) (args : List Const) :
    CekJoin (applyParams (lambdaPrefix args.length lhs) (args.map .Const))
      (applyParams (lambdaPrefix args.length rhs) (args.map .Const)) := by
  intro variant stack env
  let prefixSteps := (args.map Term.Const).length + args.length * 4
  let captured := args.foldl (fun env c => CekValue.VCon c :: env) env
  obtain ⟨leftSteps, rightSteps, same⟩ := joined variant stack captured
  refine ⟨prefixSteps + leftSteps, prefixSteps + rightSteps, ?_⟩
  rw [stepN_add variant prefixSteps leftSteps, stepN_add variant prefixSteps rightSteps]
  simpa only [prefixSteps, enterLiteralPrefix, captured] using same

private def prefixBody : (arity : Nat) → (term : Term) →
    Option { body : Term // lambdaPrefix arity body = term }
  | 0, term => some ⟨term, rfl⟩
  | arity + 1, .Lam body =>
    match prefixBody arity body with
    | some found => some ⟨found.1, congrArg Term.Lam found.2⟩
    | none => none
  | _ + 1, _ => none

/-- Optimize the root below `arity` consecutive lambda binders. The witness
covers calls supplying exactly that many literal constant arguments. Terms
with fewer enclosing lambda binders are returned without rewrites. -/
def certifiedPrefix (fuel arity : Nat) (term : Term) :
    { result : Term × Nat // ∀ args : List Const, args.length = arity →
      CekJoin (applyParams term (args.map Term.Const))
        (applyParams result.1 (args.map Term.Const)) } :=
  match prefixBody arity term with
  | none => ⟨(term, 0), fun args _ => CekJoin.refl (applyParams term (args.map Term.Const))⟩
  | some found =>
    let optimized := certifiedRoot fuel found.1
    ⟨(lambdaPrefix arity optimized.1.1, optimized.1.2), by
      intro args hArity
      simpa only [hArity, found.2] using certifiedLiteralPrefix optimized.2 args⟩

end UplcOptimizer
