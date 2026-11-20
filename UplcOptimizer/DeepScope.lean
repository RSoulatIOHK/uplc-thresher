import UplcOptimizer.ForcedBuiltin

namespace UplcOptimizer.Deep

/-- A correspondence between source and target de Bruijn indices. -/
inductive Layout
  | same
  | keep (tail : Layout)
  | insert (forced : ForcedBuiltin) (tail : Layout)

def Layout.underBinder : Layout → Layout
  | .same => .same
  | layout => .keep layout

def Layout.rename : Layout → Nat → Nat
  | .same, index => index
  | .keep _, 0 => 0
  | .keep tail, index + 1 => tail.rename index + 1
  | .insert _ tail, index => tail.rename index + 1

def Layout.hoistedAt : Layout → Nat → Option ForcedBuiltin
  | .same, _ | .keep _, 0 => none
  | .keep tail, index + 1 => tail.hoistedAt index
  | .insert forced _, 0 => some forced
  | .insert _ tail, index + 1 => tail.hoistedAt index

end UplcOptimizer.Deep
