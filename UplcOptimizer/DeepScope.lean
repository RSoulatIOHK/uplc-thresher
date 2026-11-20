import UplcOptimizer.CacheExpr
import UplcOptimizer.ForcedBuiltin

namespace UplcOptimizer.Deep

/-- A correspondence between source and target de Bruijn indices. -/
inductive Layout
  | same
  | keep (tail : Layout)
  | insert (forced : ForcedBuiltin) (tail : Layout)
  | cache (expr : CacheExpr) (tail : Layout)
  | splitPair (tail : Layout)

def Layout.underBinder : Layout → Layout
  | .same => .same
  | layout => .keep layout

def Layout.rename : Layout → Nat → Nat
  | .same, index => index
  | .keep _, 0 => 0
  | .keep tail, index + 1 => tail.rename index + 1
  | .insert _ tail, index => tail.rename index + 1
  | .cache _ tail, index => tail.rename index + 1
  | .splitPair _, 0 => 0
  | .splitPair tail, index + 1 => tail.rename index + 2

/-- A split pair has no corresponding whole-value variable on the target. -/
def Layout.varAllowed : Layout → Nat → Bool
  | .same, _ | .keep _, 0 => true
  | .keep tail, index + 1 => tail.varAllowed index
  | .insert _ tail, index | .cache _ tail, index => tail.varAllowed index
  | .splitPair _, 0 => false
  | .splitPair tail, index + 1 => tail.varAllowed index

def Layout.pairField : Layout → Nat → Bool → Option Nat
  | .same, _, _ | .keep _, 0, _ => none
  | .keep tail, index + 1, first => (tail.pairField index first).map Nat.succ
  | .insert _ tail, index, first | .cache _ tail, index, first =>
    (tail.pairField index first).map Nat.succ
  | .splitPair _, 0, first => some (if first then 1 else 0)
  | .splitPair tail, index + 1, first => (tail.pairField index first).map (· + 2)

def Layout.hoistedAt : Layout → Nat → Option ForcedBuiltin
  | .same, _ | .keep _, 0 => none
  | .keep tail, index + 1 => tail.hoistedAt index
  | .insert forced _, 0 => some forced
  | .insert _ tail, index + 1 => tail.hoistedAt index
  | .cache _ _, 0 => none
  | .cache _ tail, index + 1 => tail.hoistedAt index
  | .splitPair _, 0 | .splitPair _, 1 => none
  | .splitPair tail, index + 2 => tail.hoistedAt index

def Layout.cachedAt : Layout → Nat → Option CacheExpr
  | .same, _ | .keep _, 0 | .insert _ _, 0 => none
  | .keep tail, index + 1 => (tail.cachedAt index).map CacheExpr.shift
  | .insert _ tail, index + 1 => tail.cachedAt index
  | .cache expr _, 0 => some expr
  | .cache _ tail, index + 1 => tail.cachedAt index
  | .splitPair _, 0 | .splitPair _, 1 => none
  | .splitPair tail, index + 2 => (tail.cachedAt index).map CacheExpr.shift

end UplcOptimizer.Deep
