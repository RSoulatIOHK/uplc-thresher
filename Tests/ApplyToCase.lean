import UplcOptimizer

namespace Tests.ApplyToCase

open PlutusCore.Default
open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term
open UplcOptimizer UplcOptimizer.Deep

private def v10 : Version := .Version 1 0 0
private def v11 : Version := .Version 1 1 0

private def bodyOf : Program → Term
  | .Program _ body => body

private def integer (value : Int) : Term := .Const (.Integer value)

private def binary (builtin : BuiltinFun) (left right : Term) : Term :=
  applyParams (.Builtin builtin) [left, right]

private def divide (left right : Int) : Term :=
  binary .DivideInteger (integer left) (integer right)

private def evaluate (body : Term) (arguments : List Term := []) : State :=
  cekExecuteProgramWithSemanticVariant default (.Program v11 body) arguments 2000

private def returnsInt (term : Term) (arguments : List Term) (expected : Int) : Bool :=
  match evaluate term arguments with
  | .Halt (.VCon (.Integer result)) => result == expected
  | _ => false

private def fails (term : Term) (arguments : List Term := []) : Bool :=
  match evaluate term arguments with
  | .Error => true
  | _ => false

private def exhausts (term : Term) (arguments : List Term := []) : Bool :=
  match evaluate term arguments with
  | .BudgetExhausted => true
  | _ => false

private def digit (acc value : Term) : Term :=
  binary .AddInteger (binary .MultiplyInteger acc (integer 10)) value

-- The function captures the surrounding binder and observes the order of
-- all four arguments in the decimal digits of the result.
private def function : Term :=
  let number := digit (digit (digit (.Var 3) (.Var 2)) (.Var 1)) (.Var 0)
  .Lam (.Lam (.Lam (.Lam (binary .AddInteger (.Var 4) number))))

private def arguments : List Term :=
  [divide 21 3, divide 24 12, divide 27 9, divide 35 7]

private def batch (args : List Term) : Term := .Lam (applyParams function args)

private def packed (args : List Term) : Term := .Lam (.Case (.Constr 0 args) [function])

private def optimized (body : Term) : Term := bodyOf (optimize (.Program v11 body)).1

#guard optimized (batch arguments) == packed arguments
#guard (optimize (.Program v11 (batch arguments))).2.byRule["packLambdaApplications_sound"]? == some 1
#guard nodes (optimized (batch arguments)) + 2 == nodes (batch arguments)
#guard returnsInt (batch arguments) [integer 20] 7255
#guard returnsInt (optimized (batch arguments)) [integer 20] 7255

-- Three arguments can be packed while leaving the fourth lambda to be
-- applied by the caller. A two-argument chain stays in application form.
#guard optimized (batch (arguments.take 3)) == packed (arguments.take 3)
#guard returnsInt (optimized (batch (arguments.take 3))) [integer 20, integer 5] 7255
#guard optimized (batch (arguments.take 2)) == batch (arguments.take 2)

-- Construction and case analysis require UPLC 1.1.
private def legacy : Program := .Program v10 (batch arguments)
#guard bodyOf (optimize legacy).1 == batch arguments
#guard (optimize legacy).2.rewrites == 0

private def omega : Term :=
  let self := Term.Lam (.Apply (.Var 0) (.Var 0))
  .Apply self self

private def failFirst : List Term := [divide 1 0, omega, divide 27 9, divide 35 7]
private def loopFirst : List Term := [omega, divide 1 0, divide 27 9, divide 35 7]

-- Field evaluation must preserve the original left-to-right order.
#guard optimized (batch failFirst) == packed failFirst
#guard optimized (batch loopFirst) == packed loopFirst
#guard fails (batch failFirst) [integer 20] && fails (optimized (batch failFirst)) [integer 20]
#guard exhausts (batch loopFirst) [integer 20] && exhausts (optimized (batch loopFirst)) [integer 20]

private def earlyBody : Term := .Lam .Error
private def unsafeArgs : List Term := [divide 21 3, omega, divide 27 9, divide 35 7]
private def unsafeSpine : Term := applyParams earlyBody unsafeArgs

-- The original first application runs the body before entering omega.
-- Packing this spine would run omega while evaluating constructor fields.
#guard optimized unsafeSpine == unsafeSpine
#guard fails unsafeSpine && fails (optimized unsafeSpine)
#guard exhausts (.Case (.Constr 0 unsafeArgs) [earlyBody])

private def forcedIf : Term := .Force (.Builtin .IfThenElse)

private def conditional (yes no : Term) : Term :=
  .Lam (applyParams forcedIf [.Var 0, yes, no])

private def conditionalValues : Term := conditional (integer 17) (integer 9)

#guard optimized conditionalValues ==
  .Lam (.Case (.Constr 0 [.Var 0, integer 17, integer 9]) [forcedIf])
#guard (optimize (.Program v11 conditionalValues)).2.byRule["packConditionalApplications_sound"]? == some 1
#guard returnsInt (optimized conditionalValues) [.Const (.Bool true)] 17
#guard returnsInt (optimized conditionalValues) [.Const (.Bool false)] 9
#guard fails conditionalValues [integer 0] && fails (optimized conditionalValues) [integer 0]

private def conditionalDelay : Term := conditional (.Delay .Error) (integer 9)
private def conditionalLoop : Term := conditional (integer 17) omega

-- A delay is an immediate value. A computing arm is outside the matcher.
#guard optimized conditionalDelay ==
  .Lam (.Case (.Constr 0 [.Var 0, .Delay .Error, integer 9]) [forcedIf])
#guard returnsInt (optimized conditionalDelay) [.Const (.Bool false)] 9
#guard fails (.Force (.Apply (optimized conditionalDelay) (.Const (.Bool true))))
#guard optimized conditionalLoop == conditionalLoop
#guard exhausts conditionalLoop [.Const (.Bool true)]

private def computedCondition : Term := binary .EqualsInteger (divide 21 3) (.Var 0)

private def delayedConditional : Term :=
  .Lam (.Force (applyParams forcedIf [computedCondition, .Delay (integer 17), .Delay (integer 9)]))

#guard optimized delayedConditional ==
  .Lam (.Case (.Constr 0 [computedCondition, integer 17, integer 9]) [forcedIf])
#guard (optimize (.Program v11 delayedConditional)).2.byRule["forceIfThenElse_sound"]? == some 1
#guard (optimize (.Program v11 delayedConditional)).2.byRule["packConditionalApplications_sound"]? == some 1
#guard returnsInt (optimized delayedConditional) [integer 7] 17
#guard returnsInt (optimized delayedConditional) [integer 0] 9

private def legacyConditional : Program := .Program (.Version 1 0 7) conditionalValues
#guard bodyOf (optimize legacyConditional).1 == conditionalValues
#guard (optimize legacyConditional).2.rewrites == 0

example : ProgramEquivalent (.Program v11 (batch arguments))
    (optimize (.Program v11 (batch arguments))).1 :=
  optimize_preserves (.Program v11 (batch arguments))

/-- info: 'UplcOptimizer.optimize_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UplcOptimizer.optimize_preserves

end Tests.ApplyToCase
