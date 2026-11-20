import UplcOptimizer

namespace Tests.TaggedRules

open PlutusCore.UPLC.Term UplcOptimizer

def_uplc_rules bundledRules

@[uplc_rule] theorem forceTwoDelays (body : Term) :
    CekJoin (.Force (.Force (.Delay (.Delay body)))) body := by
  intro variant stack env
  exact ⟨6, 0, rfl⟩

@[uplc_rule] theorem subtractNegativeThree (left : Int) :
    CekJoin (.Apply (.Apply (.Builtin .SubtractInteger) (.Const (.Integer left)))
      (.Const (.Integer (-3)))) (.Const (.Integer (left - (-3)))) := by
  intro variant stack env
  exact ⟨9, 1, rfl⟩

@[uplc_rule] theorem subtractNegativeFourIfNonnegative (left : Int) (_guard : 0 ≤ left) :
    CekJoin (.Apply (.Apply (.Builtin .SubtractInteger) (.Const (.Integer left)))
      (.Const (.Integer (-4)))) (.Const (.Integer (left - (-4)))) := by
  intro variant stack env
  exact ⟨9, 1, rfl⟩

def_uplc_rules guardedRules

@[uplc_rule] theorem subtractNegativeFourIfNegative (left : Int) (_guard : left < 0) :
    CekJoin (.Apply (.Apply (.Builtin .SubtractInteger) (.Const (.Integer left)))
      (.Const (.Integer (-4)))) (.Const (.Integer (left - (-4)))) := by
  intro variant stack env
  exact ⟨9, 1, rfl⟩

def_uplc_rules extendedRules

private def integer (value : Int) : Term := .Const (.Integer value)

private def doubleForce (body : Term) : Term := .Force (.Force (.Delay (.Delay body)))

private def subtraction (left right : Int) : Term :=
  .Apply (.Apply (.Builtin .SubtractInteger) (integer left)) (integer right)

example : (bundledRules (.Force (.Delay (integer 7)))).map Subtype.val = some (integer 7) := by
  decide

example : (bundledRules (.Apply (.Lam (.Var 0)) (integer 7))).map Subtype.val = some (integer 7) := by
  decide

example : (bundledRules (.Apply (.Apply (.Builtin .AddInteger) (integer (-8))) (integer 3))).map
    Subtype.val = some (integer (-5)) := by decide

example : (bundledRules (.Case (.Constr 1 []) [integer 5, integer 7])).map Subtype.val =
    some (integer 7) := by decide

example : (bundledRules (.Case (.Constr 1 []) [integer 5])).map Subtype.val = some .Error := by
  decide

example : (bundledRules (doubleForce (integer (-11)))).isNone = true := by decide

example : (extendedRules (doubleForce (integer (-11)))).map Subtype.val = some (integer (-11)) := by
  decide

example : (extendedRules (subtraction (-8) (-3))).map Subtype.val = some (integer (-5)) := by decide

example : (extendedRules (subtraction (-8) 3)).isNone = true := by decide

example : (guardedRules (subtraction 8 (-4))).map Subtype.val = some (integer 12) := by decide

example : (guardedRules (subtraction (-8) (-4))).isNone = true := by decide

example : (extendedRules (subtraction (-8) (-4))).map Subtype.val = some (integer (-4)) := by decide

example : (extendedRules (subtraction 8 (-4))).map Subtype.val = some (integer 12) := by decide

example : (extendedRules (integer (-11))).isNone = true := by decide

example : (certifiedRootWith extendedRules 8 (doubleForce (subtraction (-8) (-3)))).val =
    (integer (-5), 2) := by decide

example : (certifiedRootWith extendedRules 1 (doubleForce (subtraction (-8) (-3)))).val =
    (subtraction (-8) (-3), 1) := by decide

/-- error: @[uplc_rule] theorem must conclude CekJoin lhs rhs -/
#guard_msgs in
@[uplc_rule] theorem unrelated : 0 = 0 := rfl

end Tests.TaggedRules
