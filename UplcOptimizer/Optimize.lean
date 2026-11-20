import UplcOptimizer.DeepBehavior
import UplcOptimizer.DeepOptimize
import UplcOptimizer.DeepRules

namespace UplcOptimizer

open PlutusCore.UPLC.Term

/-- Counts syntax nodes, including list children in constructors and cases. -/
partial def nodes : Term → Nat
  | .Lam body | .Delay body | .Force body => 1 + nodes body
  | .Apply fn arg => 1 + nodes fn + nodes arg
  | .Constr _ fields => fields.foldl (fun n field => n + nodes field) 1
  | .Case scrutinee branches =>
      branches.foldl (fun n branch => n + nodes branch) (1 + nodes scrutinee)
  | _ => 1

structure Stats where
  rewrites : Nat := 0
  sweeps : Nat := 0
  byRule : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Run the deep optimizer with a checked contextual-equivalence witness. -/
def optimizeWithProof (program : Program) (maxSweeps : Nat := 12) :
    { result : Program × Stats // Deep.ProgramEquivalent program result.1 } :=
  match program with
  | .Program version term =>
    let optimized := Deep.optimizeTerm Deep.rootRule term maxSweeps
    let counts := optimized.val.2
    let byRule := if counts.rewrites == 0 then {} else
      ({} : Std.HashMap String Nat).insert "theorem-rule" counts.rewrites
    ⟨(.Program version optimized.val.1, ⟨counts.rewrites, counts.sweeps, byRule⟩),
      optimized.property.programEquivalent version⟩

/-- Optimize a program solely by applying tagged and checked deep rewrite rules. -/
def optimize (program : Program) (maxSweeps : Nat := 12) : Program × Stats :=
  (optimizeWithProof program maxSweeps).val

theorem optimize_preserves (program : Program) (maxSweeps : Nat := 12) :
    Deep.ProgramEquivalent program (optimize program maxSweeps).1 :=
  (optimizeWithProof program maxSweeps).property

end UplcOptimizer
