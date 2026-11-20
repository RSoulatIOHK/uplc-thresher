import UplcOptimizer.DeepScope
import UplcOptimizer.Application
import UplcOptimizer.Conditional
import UplcOptimizer.Dominates

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- Prepare a syntactic value (or error) in a single transition. A computation
    remains at the head of the evaluator with the same stack and environment. -/
def prepare (stack : Stack) (env : Environment) : Term → State
  | .Const c => .Return stack (.VCon c)
  | .Lam body => .Return stack (.VLam body env)
  | .Delay body => .Return stack (.VDelay body env)
  | .Error => .Error
  | term => .Eval stack env term

def prepared : Term → Bool
  | .Const _ | .Lam _ | .Delay _ | .Error => true
  | _ => false

theorem prepare_eval {term : Term} (h : prepared term = false) (s : Stack) (env : Environment) :
    prepare s env term = .Eval s env term := by
  cases term <;> simp_all [prepared, prepare]

/-- The supported head rules contract a computation rather than a value. -/
def redex : Term → Bool
  | .Apply .. | .Force _ | .Case .. => true
  | _ => false

/-- A rule advances the old program to the head state of its replacement
    under every continuation, environment, and builtin semantics variant.
    Positive advancement is essential to the termination argument. -/
structure StepRule (lhs rhs : Term) : Prop where
  active : redex lhs = true
  advance : ∀ variant stack env, ∃ steps,
    stepN variant (steps + 1) (.Eval stack env lhs) = prepare stack env rhs

mutual
  inductive ScopedTermRel : Layout → Term → Term → Prop
    | var (n : Nat) : ScopedTermRel layout (.Var n) (.Var (layout.rename n))
    | const (c : Const) : ScopedTermRel layout (.Const c) (.Const c)
    | builtin (b : BuiltinFun) : ScopedTermRel layout (.Builtin b) (.Builtin b)
    | error : ScopedTermRel layout .Error .Error
    | lam : ScopedTermRel layout.underBinder lhs rhs → ScopedTermRel layout (.Lam lhs) (.Lam rhs)
    | delay : ScopedTermRel layout lhs rhs → ScopedTermRel layout (.Delay lhs) (.Delay rhs)
    | force : ScopedTermRel layout lhs rhs → ScopedTermRel layout (.Force lhs) (.Force rhs)
    | apply : ScopedTermRel layout lhs rhs → ScopedTermRel layout arg arg' →
        ScopedTermRel layout (.Apply lhs arg) (.Apply rhs arg')
    | constr (tag : Nat) : ScopedTermsRel layout lhs rhs →
        ScopedTermRel layout (.Constr tag lhs) (.Constr tag rhs)
    | case : ScopedTermRel layout lhs rhs → ScopedTermsRel layout bs cs →
        ScopedTermRel layout (.Case lhs bs) (.Case rhs cs)
    | reduce : StepRule lhs mid → ScopedTermRel layout mid rhs → ScopedTermRel layout lhs rhs
    | reference (forced : ForcedBuiltin) (index : Nat) :
        layout.hoistedAt index = some forced → ScopedTermRel layout forced.term (.Var index)
    | hoist (forced : ForcedBuiltin) : ScopedTermRel (.insert forced layout) lhs body →
        ScopedTermRel layout lhs (.Apply (.Lam body) forced.term)
    | forceDelaySaturated (first : Term) (rest : List Term) : ScopedTermRel .same lhs rhs →
        ScopedTermRel .same
          (.Force (applyParams (lambdaPrefix (rest.length + 1) (.Delay lhs)) (first :: rest)))
          (applyParams (lambdaPrefix (rest.length + 1) rhs) (first :: rest))
    | forceIfThenElse (condition yes no : Term) :
        immediateArm yes = true → immediateArm no = true →
        ScopedTermRel .same (.Force (ifThenElseTerm condition (.Delay yes) (.Delay no)))
          (ifThenElseTerm condition yes no)
    | packLambdaApplications (first : Term) (rest : List Term) :
        ScopedTermRel .same lhs rhs → ScopedTermRel .same
          (applyParams (lambdaPrefix (rest.length + 1) lhs) (first :: rest))
          (.Case (.Constr 0 (first :: rest)) [lambdaPrefix (rest.length + 1) rhs])
    | packConditionalApplications (condition yes no : Term) :
        immediateArm yes = true → immediateArm no = true →
        ScopedTermRel .same (ifThenElseTerm condition yes no)
          (.Case (.Constr 0 [condition, yes, no]) [.Force (.Builtin .IfThenElse)])
    | cachedReference (expr : CacheExpr) (index : Nat) :
        layout.cachedAt index = some expr → ScopedTermRel layout expr.term (.Var index)
    | shareCommonProjection (expr : CacheExpr) (first : FirstUse expr.term lhs)
        (active : prepared lhs = false) : ScopedTermRel (.cache expr .same) lhs body →
        ScopedTermRel .same lhs (.Apply (.Lam body) expr.term)

  inductive ScopedTermsRel : Layout → List Term → List Term → Prop
    | nil : ScopedTermsRel layout [] []
    | cons : ScopedTermRel layout a b → ScopedTermsRel layout as bs →
        ScopedTermsRel layout (a :: as) (b :: bs)
end

abbrev TermRel := ScopedTermRel .same
abbrev TermsRel := ScopedTermsRel .same

mutual
  theorem TermRel.refl (term : Term) : TermRel term term :=
    match term with
    | .Var n => .var n
    | .Const c => .const c
    | .Builtin b => .builtin b
    | .Error => .error
    | .Lam body => .lam (TermRel.refl body)
    | .Delay body => .delay (TermRel.refl body)
    | .Force body => .force (TermRel.refl body)
    | .Apply fn arg => .apply (TermRel.refl fn) (TermRel.refl arg)
    | .Constr tag fields => .constr tag (TermsRel.refl fields)
    | .Case scrutinee cases => .case (TermRel.refl scrutinee) (TermsRel.refl cases)
  termination_by sizeOf term

  theorem TermsRel.refl (terms : List Term) : TermsRel terms terms :=
    match terms with
    | [] => .nil
    | term :: rest => .cons (TermRel.refl term) (TermsRel.refl rest)
  termination_by sizeOf terms
end

/-- A sequence of deep sweeps. Each sweep has its own simulation derivation. -/
inductive TermRel.Chain : Term → Term → Prop
  | refl (term : Term) : Chain term term
  | step : TermRel lhs mid → Chain mid rhs → Chain lhs rhs

end UplcOptimizer.Deep
