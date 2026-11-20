import UplcOptimizer.LocalProofs

namespace UplcOptimizer.Deep

open PlutusCore.Default
open PlutusCore.UPLC.Builtins
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term

/-- The entire leading type-argument prefix, stopping at a value argument.
A final `.One .ArgQ` is deliberately excluded because forcing it executes
the builtin instead of merely updating the builtin value. -/
inductive ForcePrefix : ExpectedBuiltinArgs → Nat → ExpectedBuiltinArgs → Prop where
  | oneValue : ForcePrefix (.One .ArgV) 0 (.One .ArgV)
  | moreValues : ForcePrefix (.More .ArgV rest) 0 (.More .ArgV rest)
  | force : ForcePrefix initial count remaining →
      ForcePrefix (.More .ArgQ initial) (count + 1) remaining

structure ForcedBuiltin where
  builtin : BuiltinFun
  forces : Nat
  expected : ExpectedBuiltinArgs
  positive : 0 < forces
  leading : ForcePrefix (expectedArgs builtin) forces expected

private def forcePrefix? : (args : ExpectedBuiltinArgs) →
    Option { found : Nat × ExpectedBuiltinArgs // ForcePrefix args found.1 found.2 }
  | .One .ArgV => some ⟨(0, .One .ArgV), .oneValue⟩
  | .One .ArgQ => none
  | .More .ArgV rest => some ⟨(0, .More .ArgV rest), .moreValues⟩
  | .More .ArgQ rest => do
    let found ← forcePrefix? rest
    return ⟨(found.val.1 + 1, found.val.2), .force found.property⟩

private def findForcedBuiltin (builtin : BuiltinFun) :
    Option { forced : ForcedBuiltin // forced.builtin = builtin } := do
  let found ← forcePrefix? (expectedArgs builtin)
  if positive : 0 < found.val.1 then
    some ⟨⟨builtin, found.val.1, found.val.2, positive, found.property⟩, rfl⟩
  else
    none

def ForcedBuiltin.find? (builtin : BuiltinFun) : Option ForcedBuiltin :=
  (findForcedBuiltin builtin).map Subtype.val

private def forceTerm (term : Term) : Nat → Term
  | 0 => term
  | count + 1 => .Force (forceTerm term count)

def ForcedBuiltin.term (forced : ForcedBuiltin) : Term :=
  forceTerm (.Builtin forced.builtin) forced.forces

def ForcedBuiltin.value (forced : ForcedBuiltin) : CekValue :=
  .VBuiltin forced.builtin [] forced.expected

private def peelForces : (term : Term) →
    Option { found : BuiltinFun × Nat // term = forceTerm (.Builtin found.1) found.2 }
  | .Builtin builtin => some ⟨(builtin, 0), rfl⟩
  | .Force body => do
    let inner ← peelForces body
    return ⟨(inner.val.1, inner.val.2 + 1), congrArg Term.Force inner.property⟩
  | _ => none

/-- Recognize a raw term with exactly the full force prefix. A partially or
over-forced application is not itself a hoisting candidate. -/
def ForcedBuiltin.match? (term : Term) : Option { forced : ForcedBuiltin // term = forced.term } := do
  let chain ← peelForces term
  let forced ← findForcedBuiltin chain.val.1
  if sameCount : chain.val.2 = forced.val.forces then
    some ⟨forced.val, chain.property.trans (by rw [ForcedBuiltin.term, forced.property, sameCount])⟩
  else
    none

private def forceStack : Nat → Stack → Stack
  | 0, stack => stack
  | count + 1, stack => .ForceFrame :: forceStack count stack

private theorem forceStack_push (count : Nat) (stack : Stack) :
    forceStack count (.ForceFrame :: stack) = .ForceFrame :: forceStack count stack := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change .ForceFrame :: forceStack count (.ForceFrame :: stack) =
      .ForceFrame :: .ForceFrame :: forceStack count stack
    rw [ih]

private theorem enterForcedBuiltin (variant : BuiltinSemanticsVariant) (count : Nat)
    (builtin : BuiltinFun) (stack : Stack) (env : Environment) :
    stepN variant (count + 1) (.Eval stack env (forceTerm (.Builtin builtin) count)) =
      .Return (forceStack count stack) (.VBuiltin builtin [] (expectedArgs builtin)) := by
  induction count generalizing stack with
  | zero => rfl
  | succ count ih =>
    change stepN variant (count + 1)
      (.Eval (.ForceFrame :: stack) env (forceTerm (.Builtin builtin) count)) = _
    rw [ih, forceStack_push]
    rfl

private theorem ForcePrefix.run {initial count remaining}
    (leading : ForcePrefix initial count remaining) (variant : BuiltinSemanticsVariant)
    (builtin : BuiltinFun) (stack : Stack) :
    stepN variant count (.Return (forceStack count stack) (.VBuiltin builtin [] initial)) =
      .Return stack (.VBuiltin builtin [] remaining) := by
  induction leading with
  | oneValue | moreValues => rfl
  | force _ ih => exact ih

/-- A fully forced builtin is closed and evaluates to its partial builtin
value without calling the builtin, even with an arbitrary CEK continuation. -/
theorem ForcedBuiltin.evaluate (forced : ForcedBuiltin) (variant : BuiltinSemanticsVariant)
    (stack : Stack) (env : Environment) :
    stepN variant (2 * forced.forces + 1) (.Eval stack env forced.term) =
      .Return stack forced.value := by
  have split : 2 * forced.forces + 1 = (forced.forces + 1) + forced.forces := by omega
  rw [split, stepN_add]
  change stepN variant forced.forces
    (stepN variant (forced.forces + 1) (.Eval stack env
      (forceTerm (.Builtin forced.builtin) forced.forces))) = _
  rw [enterForcedBuiltin]
  exact forced.leading.run variant forced.builtin stack

/-- Enter an immediately applied lambda whose argument initializes this
builtin. No outer continuation is evaluated during the prologue. -/
theorem ForcedBuiltin.enterLet (forced : ForcedBuiltin) (variant : BuiltinSemanticsVariant)
    (stack : Stack) (env : Environment) (body : Term) :
    stepN variant (2 * forced.forces + 5)
      (.Eval stack env (.Apply (.Lam body) forced.term)) =
      .Eval stack (forced.value :: env) body := by
  have split : 2 * forced.forces + 5 = (3 + (2 * forced.forces + 1)) + 1 := by omega
  rw [split, stepN_add, stepN_add]
  change stepN variant 1
    (stepN variant (2 * forced.forces + 1)
      (.Eval (.RightApplicationOfValue (.VLam body env) :: stack) env forced.term)) = _
  rw [forced.evaluate]
  rfl

end UplcOptimizer.Deep
