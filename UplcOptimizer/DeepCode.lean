import UplcOptimizer.LocalProofs

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
  inductive TermRel : Term → Term → Prop
    | var (n : Nat) : TermRel (.Var n) (.Var n)
    | const (c : Const) : TermRel (.Const c) (.Const c)
    | builtin (b : BuiltinFun) : TermRel (.Builtin b) (.Builtin b)
    | error : TermRel .Error .Error
    | lam : TermRel lhs rhs → TermRel (.Lam lhs) (.Lam rhs)
    | delay : TermRel lhs rhs → TermRel (.Delay lhs) (.Delay rhs)
    | force : TermRel lhs rhs → TermRel (.Force lhs) (.Force rhs)
    | apply : TermRel lhs rhs → TermRel arg arg' → TermRel (.Apply lhs arg) (.Apply rhs arg')
    | constr (tag : Nat) : TermsRel lhs rhs → TermRel (.Constr tag lhs) (.Constr tag rhs)
    | case : TermRel lhs rhs → TermsRel bs cs → TermRel (.Case lhs bs) (.Case rhs cs)
    | reduce : StepRule lhs mid → TermRel mid rhs → TermRel lhs rhs

  inductive TermsRel : List Term → List Term → Prop
    | nil : TermsRel [] []
    | cons : TermRel a b → TermsRel as bs → TermsRel (a :: as) (b :: bs)
end

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
