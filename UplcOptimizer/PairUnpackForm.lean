import PlutusCore.UPLC.Term

namespace UplcOptimizer.Deep

open PlutusCore.UPLC.Term

def unConstrDataTerm (arg : Term) : Term := .Apply (.Builtin .UnConstrData) arg

/-- A direct projection using the integer tag and fields returned by unConstrData. -/
def pairProjection (index : Nat) (first : Bool) : Term :=
  .Case (.Var index) [.Lam (.Lam (.Var (if first then 1 else 0)))]

end UplcOptimizer.Deep
