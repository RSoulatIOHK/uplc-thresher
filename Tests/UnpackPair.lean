import UplcOptimizer

namespace Tests.UnpackPair

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term
open UplcOptimizer UplcOptimizer.Deep

private def program : Term → Program := .Program (.Version 1 1 0)

private def integer (value : Int) : Term := .Const (.Integer value)

private def datum : Term := .Const (.Data (.Constr 19 [.I 41]))
private def malformed : Term := .Const (.Data (.I 41))

private def unConstr (data : Term) : Term := .Apply (.Builtin .UnConstrData) data

private def first (pair : Term) : Term := .Case pair [.Lam (.Lam (.Var 1))]
private def second (pair : Term) : Term := .Case pair [.Lam (.Lam (.Var 0))]

private def payload (items : Term) : Term :=
  .Apply (.Builtin .UnIData) (.Apply (.Force (.Builtin .HeadList)) items)

private def binary (op : BuiltinFun) (left right : Term) : Term :=
  applyParams (.Builtin op) [left, right]

private def destructure (data body : Term) : Term := .Apply (.Lam body) (unConstr data)

private def packed (data body : Term) : Term :=
  .Case (unConstr data) [.Lam (.Lam body)]

private def bodyOf : Program → Term
  | .Program _ body => body

private def optimized (body : Term) : Term := bodyOf (optimize (program body)).1

private def unpackings (script : Program) : Nat :=
  ((optimize script).2.byRule["unpackPairLet_sound"]?).getD 0

private def evaluate (term : Term) (args : List Term) : State :=
  cekExecuteProgramWithSemanticVariant default (program term) args 2000

private def returnsInt (term : Term) (args : List Term) (expected : Int) : Bool :=
  match evaluate term args with
  | .Halt (.VCon (.Integer value)) => value == expected
  | _ => false

private def errors (term : Term) (args : List Term := []) : Bool :=
  match evaluate term args with
  | .Error => true
  | _ => false

private def exhausts (term : Term) (args : List Term := []) : Bool :=
  match evaluate term args with
  | .BudgetExhausted => true
  | _ => false

private def ambient : Term := .Lam (.Lam
  (destructure (.Var 0) (binary .AddInteger (.Var 2)
    (binary .SubtractInteger (first (.Var 0)) (payload (second (.Var 0)))))))

private def ambientPacked : Term := .Lam (.Lam
  (packed (.Var 0) (binary .AddInteger (.Var 3)
    (binary .SubtractInteger (.Var 1) (payload (.Var 0))))))

-- Adding the second component binder shifts the ambient integer reference.
#guard unpackings (program ambient) == 1
#guard optimized ambient == ambientPacked
#guard returnsInt ambient [integer 12, datum] (-10)
#guard returnsInt (optimized ambient) [integer 12, datum] (-10)
#guard errors ambient [integer 12, malformed] && errors (optimized ambient) [integer 12, malformed]

private def captured : Term := .Lam (destructure (.Var 0) (.Lam
  (binary .SubtractInteger (binary .AddInteger (first (.Var 1)) (payload (second (.Var 1)))) (.Var 0))))

private def capturedPacked : Term := .Lam (packed (.Var 0) (.Lam
  (binary .SubtractInteger (binary .AddInteger (.Var 2) (payload (.Var 1))) (.Var 0))))

#guard unpackings (program captured) == 1
#guard optimized captured == capturedPacked
#guard returnsInt captured [datum, integer 12] 48
#guard returnsInt (optimized captured) [datum, integer 12] 48

-- The in-memory optimizer must gate construction of the new case by version.
private def legacy : Program := .Program (.Version 1 0 0) ambient
#guard unpackings legacy == 0
#guard bodyOf (optimize legacy).1 == ambient

private def wholePair : Term :=
  .Lam (destructure (.Var 0) (.Constr 0 [first (.Var 0), .Var 0]))

private def nonProjection : Term := .Lam (destructure (.Var 0)
  (.Constr 0 [first (.Var 0), .Case (.Var 0) [.Lam (.Lam (binary .AddInteger (.Var 1) (integer 1)))]]))

private def singleProjection : Term := .Lam (destructure (.Var 0) (first (.Var 0)))

#guard unpackings (program wholePair) == 0
#guard optimized wholePair == wholePair
#guard unpackings (program nonProjection) == 0
#guard optimized nonProjection == nonProjection
#guard unpackings (program singleProjection) == 0
#guard optimized singleProjection == singleProjection

private def omega : Term :=
  let self := Term.Lam (.Apply (.Var 0) (.Var 0))
  .Apply self self

private def strictArgument : Term := .Lam (destructure (.Var 0)
  (.Constr 0 [omega, first (.Var 0), payload (second (.Var 0))]))

-- A failed destructuring argument prevents evaluation of the divergent body.
#guard unpackings (program strictArgument) == 1
#guard errors strictArgument [malformed] && errors (optimized strictArgument) [malformed]
#guard exhausts strictArgument [datum] && exhausts (optimized strictArgument) [datum]

private def loopingArgument : Term :=
  destructure omega (.Constr 0 [.Error, first (.Var 0), payload (second (.Var 0))])

#guard unpackings (program loopingArgument) == 1
#guard exhausts loopingArgument && exhausts (optimized loopingArgument)

private def opaqueFunction : Term :=
  let body := binary .AddInteger (first (.Var 0)) (payload (second (.Var 0)))
  let fn := .Apply (.Lam (.Lam body)) omega
  .Apply fn (unConstr malformed)

-- Evaluating this function head diverges before its malformed data argument.
#guard unpackings (program opaqueFunction) == 0
#guard exhausts opaqueFunction && exhausts (optimized opaqueFunction)

example : ProgramEquivalent (program captured) (optimize (program captured)).1 :=
  optimize_preserves (program captured)

/-- info: 'UplcOptimizer.optimize_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UplcOptimizer.optimize_preserves

end Tests.UnpackPair
