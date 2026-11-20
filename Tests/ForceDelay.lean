import UplcOptimizer

namespace Tests.ForceDelay

open UplcOptimizer UplcOptimizer.Deep PlutusCore.Default
open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term

private def program : Term → Program := .Program (.Version 1 1 0)

private def bodyOf : Program → Term
  | .Program _ body => body

private def integer (value : Int) : Term := .Const (.Integer value)

private def binary (builtin : BuiltinFun) (left right : Term) : Term :=
  .Apply (.Apply (.Builtin builtin) left) right

private def divide (left right : Int) : Term :=
  binary .DivideInteger (integer left) (integer right)

private def result (script : Program) (args : List Term := []) : State :=
  cekExecuteProgramWithSemanticVariant default script args 2000

private def haltsAt (expected : Int) (script : Program) (args : List Term := []) : Bool :=
  match result script args with
  | .Halt (.VCon (.Integer found)) => found == expected
  | _ => false

private def errors (script : Program) : Bool :=
  match result script with
  | .Error => true
  | _ => false

private def exhausts (script : Program) : Bool :=
  match result script with
  | .BudgetExhausted => true
  | _ => false

private def returnsDelay (script : Program) : Bool :=
  match result script with
  | .Halt (.VDelay ..) => true
  | _ => false

private def unary : Term :=
  .Force (.Apply (.Lam (.Delay (.Var 0))) (divide 21 3))

private def unaryOptimized : Term :=
  .Apply (.Lam (.Var 0)) (divide 21 3)

#guard bodyOf (optimize (program unary)).1 == unaryOptimized
#guard nodes (bodyOf (optimize (program unary)).1) + 2 == nodes unary
#guard (optimize (program unary)).2.rewrites == 1
#guard (optimize (program unary)).2.byRule["forceDelaySaturated_sound"]? == some 1
#guard haltsAt 7 (program unary)
#guard haltsAt 7 (optimize (program unary)).1

-- Both delayed variables and the outer binder must keep their original indices.
-- Division is an actual CEK computation, so neither argument is a syntactic value.
private def nested : Term :=
  let body := binary .SubtractInteger (binary .AddInteger (.Var 2) (.Var 1)) (.Var 0)
  .Lam (.Force (applyParams (.Lam (.Lam (.Delay body))) [divide 40 5, divide 63 7]))

private def nestedOptimized : Term :=
  let body := binary .SubtractInteger (binary .AddInteger (.Var 2) (.Var 1)) (.Var 0)
  .Lam (applyParams (.Lam (.Lam body)) [divide 40 5, divide 63 7])

#guard bodyOf (optimize (program nested)).1 == nestedOptimized
#guard haltsAt 12 (program nested) [integer 13]
#guard haltsAt 12 (optimize (program nested)).1 [integer 13]

private def omega : Term :=
  let self := Term.Lam (.Apply (.Var 0) (.Var 0))
  .Apply self self

private def saturated (first second body : Term) : Program :=
  program (.Force (applyParams (.Lam (.Lam (.Delay body))) [first, second]))

-- The first strict argument fails before the second or the suspended body
-- can diverge. Swapping the arguments changes the reference outcome.
private def firstFails : Program := saturated (divide 1 0) omega omega
private def firstLoops : Program := saturated omega (divide 1 0) (integer 10)

#guard (optimize firstFails).2.rewrites > 0
#guard (optimize firstLoops).2.rewrites > 0
#guard errors firstFails && errors (optimize firstFails).1
#guard exhausts firstLoops && exhausts (optimize firstLoops).1

private def twoDelays : Term :=
  .Force (.Apply (.Lam (.Delay (.Delay .Error))) (divide 21 3))

-- Cancel the matched delay only. The remaining delay still defers its error.
#guard bodyOf (optimize (program twoDelays)).1 == .Apply (.Lam (.Delay .Error)) (divide 21 3)
#guard returnsDelay (program twoDelays) && returnsDelay (optimize (program twoDelays)).1
#guard errors (program (.Force twoDelays)) && errors (optimize (program (.Force twoDelays))).1

private def tooFew : Term :=
  .Force (.Apply (.Lam (.Lam (.Delay (.Var 0)))) (divide 21 3))

private def tooMany : Term :=
  .Force (applyParams (.Lam (.Delay (.Var 0))) [divide 21 3, divide 8 2])

#guard bodyOf (optimize (program tooFew)).1 == tooFew
#guard bodyOf (optimize (program tooMany)).1 == tooMany
#guard (optimize (program tooFew)).2.rewrites == 0
#guard (optimize (program tooMany)).2.rewrites == 0
#guard errors (program tooFew) && errors (program tooMany)

example : ProgramEquivalent (program nested) (optimize (program nested)).1 :=
  (optimizeWithProof (program nested)).property

/-- info: 'UplcOptimizer.optimize_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UplcOptimizer.optimize_preserves

end Tests.ForceDelay
