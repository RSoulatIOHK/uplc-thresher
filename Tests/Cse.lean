import UplcOptimizer

namespace Tests.Cse

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term
open UplcOptimizer UplcOptimizer.Deep

private def program : Term → Program := .Program (.Version 1 1 0)

private def integer (value : Int) : Term := .Const (.Integer value)

private def dataInteger (value : Int) : Term := .Const (.Data (.I value))

private def projection (data : Term) : Term := .Apply (.Builtin .UnIData) data

private def evaluate (term : Term) (arguments : List Term := []) : State :=
  cekExecuteProgramWithSemanticVariant default (program term) arguments 2000

private def optimized (term : Term) : Term :=
  match (optimize (program term)).1 with
  | .Program _ body => body

private def shares (term : Term) : Nat :=
  ((optimize (program term)).2.byRule["shareCommonProjection_sound"]?).getD 0

private def returnsTwoInts (term arg : Term) (expected : Int) : Bool :=
  match evaluate term [arg] with
  | .Halt (.VConstr 0 [.VCon (.Integer first), .VCon (.Integer second)]) =>
    first == expected && second == expected
  | _ => false

private def returnsInt (term : Term) (expected : Int) : Bool :=
  match evaluate term with
  | .Halt (.VCon (.Integer found)) => found == expected
  | _ => false

private def errors (term : Term) (arguments : List Term := []) : Bool :=
  match evaluate term arguments with
  | .Error => true
  | _ => false

private def exhausts (term : Term) : Bool :=
  match evaluate term with
  | .BudgetExhausted => true
  | _ => false

private def duplicate : Term :=
  .Lam (.Constr 0 [projection (.Var 0), projection (.Var 0)])

#guard shares duplicate == 1
#guard returnsTwoInts duplicate (dataInteger 41) 41
#guard returnsTwoInts (optimized duplicate) (dataInteger 41) 41
#guard errors duplicate [integer 41] && errors (optimized duplicate) [integer 41]

private def binary (arith : BuiltinFun) (left right : Term) : Term :=
  applyParams (.Builtin arith) [left, right]

private def underLambda : Term :=
  .Lam (.Constr 0
    [projection (.Var 0), .Lam (binary .SubtractInteger (projection (.Var 1)) (.Var 0))])

private def callStoredLambda (term : Term) : Term :=
  .Case (.Apply term (dataInteger 41))
    [.Lam (.Lam (binary .AddInteger (.Var 1) (.Apply (.Var 0) (integer 12))))]

#guard shares underLambda == 1
#guard returnsInt (callStoredLambda underLambda) 70
#guard returnsInt (callStoredLambda (optimized underLambda)) 70

private def shadowed : Term :=
  .Lam (.Constr 0 [projection (.Var 0), .Lam (projection (.Var 0))])

-- The second projection uses the inner lambda's argument.
#guard shares shadowed == 0
#guard errors (callStoredLambda shadowed) && errors (callStoredLambda (optimized shadowed))

private def underDelay : Term :=
  .Lam (.Constr 0 [projection (.Var 0), .Delay (projection (.Var 0))])

private def forceStoredDelay (term : Term) : Term :=
  .Case (.Apply term (dataInteger 41)) [.Lam (.Lam (binary .AddInteger (.Var 1) (.Force (.Var 0))))]

#guard shares underDelay == 1
#guard returnsInt (forceStoredDelay underDelay) 82
#guard returnsInt (forceStoredDelay (optimized underDelay)) 82

private def demandedArgument : Term :=
  .Lam (.Apply (.Lam (.Constr 0 [.Var 0, projection (.Var 1)])) (projection (.Var 0)))

#guard shares demandedArgument == 1
#guard returnsTwoInts demandedArgument (dataInteger 19) 19
#guard returnsTwoInts (optimized demandedArgument) (dataInteger 19) 19

private def omega : Term :=
  let self := Term.Lam (.Apply (.Var 0) (.Var 0))
  .Apply self self

private def preceded (first : Term) : Term :=
  let invalid := projection (integer 41)
  .Constr 0 [first, invalid, invalid]

-- Evaluating a projection before the first field would change a divergent
-- program into a failing one.
#guard shares (preceded omega) == 0
#guard exhausts (preceded omega) && exhausts (optimized (preceded omega))
#guard shares (preceded .Error) == 0
#guard errors (preceded .Error) && errors (optimized (preceded .Error))

private def deferredOnly : Term :=
  let invalid := projection (integer 41)
  .Constr 0 [.Delay invalid, .Delay invalid]

#guard shares deferredOnly == 0
#guard optimized deferredOnly == deferredOnly

private def tracedProjection : Term :=
  .Lam (.Constr 0 (List.replicate 2 (projection
    (applyParams (.Force (.Builtin .Trace)) [.Const (.String "projection"), .Var 0]))))

#guard shares tracedProjection == 0
#guard optimized tracedProjection == tracedProjection

example : ProgramEquivalent (program underLambda) (optimize (program underLambda)).1 :=
  optimize_preserves (program underLambda)

/-- info: 'UplcOptimizer.optimize_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UplcOptimizer.optimize_preserves

end Tests.Cse
