import UplcOptimizer

namespace Tests.ForceIf

open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term
open UplcOptimizer UplcOptimizer.Deep

private def program : Term → Program := .Program (.Version 1 1 0)

private def integer (value : Int) : Term := .Const (.Integer value)

private def boolean (value : Bool) : Term := .Const (.Bool value)

private def choose (condition yes no : Term) : Term :=
  applyParams (.Force (.Builtin .IfThenElse)) [condition, yes, no]

private def chooseDelayed (condition yes no : Term) : Term :=
  .Force (choose condition (.Delay yes) (.Delay no))

private def dynamic (yes no : Term) : Term :=
  .Lam (chooseDelayed (.Var 0) yes no)

private def optimizedBody (body : Term) : Term :=
  match (optimize (program body)).1 with
  | .Program _ output => output

private def evaluate (term : Term) (arguments : List Term := []) : State :=
  cekExecuteProgramWithSemanticVariant default (program term) arguments 2000

private def returnsInt (term argument : Term) (expected : Int) : Bool :=
  match evaluate term [argument] with
  | .Halt (.VCon (.Integer result)) => result == expected
  | _ => false

private def returnsDelay (term argument : Term) : Bool :=
  match evaluate term [argument] with
  | .Halt (.VDelay ..) => true
  | _ => false

private def fails (term : Term) (arguments : List Term := []) : Bool :=
  match evaluate term arguments with
  | .Error => true
  | _ => false

private def exhausts (term : Term) (arguments : List Term := []) : Bool :=
  match evaluate term arguments with
  | .BudgetExhausted => true
  | _ => false

private def values : Term := dynamic (integer 17) (integer 9)

-- A bound condition reaches the delayed conditional matcher.
#guard optimizedBody values == .Lam (choose (.Var 0) (integer 17) (integer 9))
#guard nodes (optimizedBody values) + 3 == nodes values
#guard returnsInt values (boolean true) 17 && returnsInt (optimizedBody values) (boolean true) 17
#guard returnsInt values (boolean false) 9 && returnsInt (optimizedBody values) (boolean false) 9
#guard fails values [integer 0] && fails (optimizedBody values) [integer 0]

private def omega : Term :=
  let self := Term.Lam (.Apply (.Var 0) (.Var 0))
  .Apply self self

private def nestedDelays : Term := dynamic (.Delay .Error) (.Delay omega)

private def forceResult (body : Term) (choice : Bool) : Term :=
  .Force (.Apply body (boolean choice))

-- The selected inner delay still suspends its body after cancellation.
#guard optimizedBody nestedDelays == .Lam (choose (.Var 0) (.Delay .Error) (.Delay omega))
#guard returnsDelay nestedDelays (boolean true)
#guard returnsDelay (optimizedBody nestedDelays) (boolean true)
#guard returnsDelay nestedDelays (boolean false)
#guard returnsDelay (optimizedBody nestedDelays) (boolean false)
#guard fails (forceResult nestedDelays true) && fails (forceResult (optimizedBody nestedDelays) true)
#guard exhausts (forceResult nestedDelays false) && exhausts (forceResult (optimizedBody nestedDelays) false)

private def failingArm : Term := dynamic (integer 7) .Error
private def loopingArm : Term := dynamic (integer 7) omega

-- Exposing a non-value arm can evaluate it under call-by-value even when
-- the condition selects the other arm.
#guard optimizedBody failingArm == failingArm
#guard optimizedBody loopingArm == loopingArm
#guard returnsInt failingArm (boolean true) 7 && returnsInt loopingArm (boolean true) 7
#guard fails failingArm [boolean false] && exhausts loopingArm [boolean false]
#guard fails loopingArm [integer 0]

private def foldedCondition : Term :=
  let condition := applyParams (.Builtin .EqualsInteger) [integer 5, integer 5]
  chooseDelayed condition (integer 17) (integer 9)

#guard optimizedBody foldedCondition == integer 17
#guard (optimize (program foldedCondition)).2.byRule["forceIfThenElse_sound"]?.isNone

private def sharedConditionals : Term :=
  .Lam (.Constr 0 (List.replicate 5 (chooseDelayed (.Var 0) (integer 17) (integer 9))))

#guard (optimize (program sharedConditionals)).2.byRule["forceIfThenElse_sound"]? == some 5
#guard (optimize (program sharedConditionals)).2.byRule["hoistPolyBuiltin_sound"]? == some 1

example : ProgramEquivalent (program nestedDelays) (optimize (program nestedDelays)).1 :=
  optimize_preserves (program nestedDelays)

/-- info: 'UplcOptimizer.optimize_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UplcOptimizer.optimize_preserves

end Tests.ForceIf
