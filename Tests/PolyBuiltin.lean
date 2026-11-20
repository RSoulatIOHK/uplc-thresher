import UplcOptimizer

namespace Tests.PolyBuiltin

open UplcOptimizer UplcOptimizer.Deep PlutusCore.Default
open PlutusCore.UPLC.CekMachine PlutusCore.UPLC.CekValue PlutusCore.UPLC.Term

private def bodyOf : Program → Term
  | .Program _ body => body

private def version : Version := .Version 1 1 0

private def integer (n : Int) : Term := .Const (.Integer n)

private def fullyForced : Term → Option (Nat × BuiltinFun)
  | .Builtin builtin => some (0, builtin)
  | .Force arg => (fullyForced arg).map fun (count, builtin) => (count + 1, builtin)
  | _ => none

/-- Count maximal raw force chains, without counting a chain's proper suffixes. -/
private partial def rawCount (wanted : BuiltinFun) (forces : Nat) (term : Term) : Nat :=
  match fullyForced term with
  | some (count, builtin) => if builtin == wanted && count == forces then 1 else 0
  | none =>
    match term with
    | .Lam body | .Delay body | .Force body => rawCount wanted forces body
    | .Apply fn arg => rawCount wanted forces fn + rawCount wanted forces arg
    | .Constr _ fields => (fields.map (rawCount wanted forces)).sum
    | .Case scrutinee branches =>
      rawCount wanted forces scrutinee + (branches.map (rawCount wanted forces)).sum
    | _ => 0

private def choose (cond left right : Term) : Term :=
  .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) cond) left) right

private def observeInts (program : Program) : Option (List Int) :=
  match cekExecuteProgramWithSemanticVariant default program [] 2000 with
  | .Halt (.VConstr 0 values) => values.mapM fun
    | .VCon (.Integer n) => some n
    | _ => none
  | _ => none

-- Three pre-existing indices under nested binders and a delay must keep their
-- meanings when a fresh forced builtin binding is introduced outside them.
private def scopedFixture (condition : Bool) : Program :=
  let fields := List.replicate 8 (choose (.Var 0) (.Var 2) (.Var 1)) ++ [.Var 1, .Var 2]
  let body := Term.Lam (.Lam (.Lam (.Delay (.Constr 0 fields))))
  .Program version (.Force (applyParams body [integer 13, integer 42, .Const (.Bool condition)]))

#guard rawCount .IfThenElse 1 (bodyOf (scopedFixture true)) == 8
#guard rawCount .IfThenElse 1 (bodyOf (optimize (scopedFixture true)).1) == 1
#guard observeInts (scopedFixture true) == some (List.replicate 8 13 ++ [42, 13])
#guard observeInts (optimize (scopedFixture true)).1 == some (List.replicate 8 13 ++ [42, 13])
#guard observeInts (optimize (scopedFixture false)).1 == some (List.replicate 8 42 ++ [42, 13])

private def fstPairPartial : Term := .Force (.Builtin .FstPair)

private def mixedForceArity : Program := .Program version
  (.Constr 0 (List.replicate 8 (.Force fstPairPartial) ++ [fstPairPartial, .Builtin .FstPair]))

-- Only the two-force chain reaches a builtin's first term argument slot.
#guard rawCount .FstPair 2 (bodyOf (optimize mixedForceArity).1) == 1
#guard rawCount .FstPair 1 (bodyOf (optimize mixedForceArity).1) == 1
#guard rawCount .FstPair 0 (bodyOf (optimize mixedForceArity).1) == 1

private def plain : Program := .Program version (.Lam (.Apply (.Builtin .AddInteger) (.Var 0)))

#guard bodyOf (optimize plain).1 == bodyOf plain
#guard (optimize plain).2.rewrites == 0

private def cold : Program := .Program (.Version 1 0 0) (.Lam (choose (.Var 0) (integer 1) (integer 2)))

#guard bodyOf (optimize cold).1 == bodyOf cold

private def binary (builtin : BuiltinFun) (left right : Term) : Term :=
  .Apply (.Apply (.Builtin builtin) left) right

private def countdown : Program :=
  let recursive := Term.Apply (.Apply (.Var 1) (.Var 1))
    (binary .SubtractInteger (.Var 0) (integer 1))
  let loop := Term.Lam (.Lam (.Force (choose
    (binary .LessThanEqualsInteger (.Var 0) (integer 0)) (.Delay (integer 13)) (.Delay recursive))))
  let fix := Term.Apply (.Lam (.Apply (.Var 0) (.Var 0))) loop
  .Program version (.Apply fix (integer 8))

private def hasHoistedConditional : Term → Bool
  | .Apply (.Lam _) arg => fullyForced arg == some (1, .IfThenElse)
  | _ => false

private def haltsAt (expected : Int) (program : Program) : Bool :=
  match cekExecuteProgramWithSemanticVariant default program [] 2000 with
  | .Halt (.VCon (.Integer n)) => n == expected
  | _ => false

-- A single syntactic occurrence may run repeatedly inside a recursive closure.
#guard rawCount .IfThenElse 1 (bodyOf countdown) == 1
#guard hasHoistedConditional (bodyOf (optimize countdown).1)
#guard haltsAt 13 countdown
#guard haltsAt 13 (optimize countdown).1

private def callTrace (message : String) (result : Int) : Term :=
  .Apply (.Apply (.Force (.Builtin .Trace)) (.Const (.String message))) (integer result)

private def traceFixture : Program := .Program version
  (.Constr 0 ((List.range 8).map fun i => callTrace (toString i) (Int.ofNat i)))

private partial def traceCalls (index : Nat) : Term → List String
  | .Apply (.Apply (.Var target) (.Const (.String message))) result =>
    (if target == index then [message] else []) ++ traceCalls index result
  | .Lam body => traceCalls (index + 1) body
  | .Delay body | .Force body => traceCalls index body
  | .Apply fn arg => traceCalls index fn ++ traceCalls index arg
  | .Constr _ fields => fields.flatMap (traceCalls index)
  | .Case scrutinee branches => traceCalls index scrutinee ++ branches.flatMap (traceCalls index)
  | _ => []

private def boundTraceMessages : Term → List String
  | .Apply (.Lam body) arg =>
    if fullyForced arg == some (1, .Trace) then traceCalls 0 body else []
  | _ => []

-- The pinned CEK observes the application result. The syntactic assertion
-- checks that each message is still applied in order to the hoisted trace value.
#guard rawCount .Trace 1 (bodyOf (optimize traceFixture).1) == 1
#guard boundTraceMessages (bodyOf (optimize traceFixture).1) == (List.range 8).map toString
#guard observeInts (optimize traceFixture).1 == some ((List.range 8).map Int.ofNat)

private def multipleBindings : Program := .Program version
  (.Force (.Apply (.Lam (.Delay (.Constr 0
    (List.replicate 8 (choose (.Var 0) (integer 1) (integer 2)) ++
      (List.range 8).map fun i => callTrace (toString i) (Int.ofNat i)))))
    (.Const (.Bool false))))

#guard rawCount .IfThenElse 1 (bodyOf (optimize multipleBindings).1) == 1
#guard rawCount .Trace 1 (bodyOf (optimize multipleBindings).1) == 1
#guard observeInts (optimize multipleBindings).1 == some (List.replicate 8 2 ++ (List.range 8).map Int.ofNat)
#guard bodyOf (optimize multipleBindings 0).1 == bodyOf multipleBindings

example (program : Program) : ProgramEquivalent program (optimize program).1 :=
  (optimizeWithProof program).property

/-- info: 'UplcOptimizer.optimize_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UplcOptimizer.optimize_preserves

end Tests.PolyBuiltin
