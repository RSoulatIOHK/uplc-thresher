import PlutusCore.UPLC.Term

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

def ifThenElseTerm (condition yes no : Term) : Term :=
  .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) condition) yes) no

/-- Evaluating one of these forms returns a value without running its body. -/
def immediateArm : Term → Bool
  | .Const _ | .Lam _ | .Delay _ => true
  | _ => false

end UplcOptimizer.Deep
