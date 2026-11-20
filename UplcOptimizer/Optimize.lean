import UplcOptimizer.DeepBehavior
import UplcOptimizer.DeepOptimize
import UplcOptimizer.DeepRules
import UplcOptimizer.ForceDelay
import UplcOptimizer.ForceIf
import UplcOptimizer.PolyBuiltin

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
      Deep.forceDelayRule (some Deep.forceIfRule)
    let counts := optimized.val.2
    let localSteps := counts.rewrites - counts.contextualRules.length
    let byRule : Std.HashMap String Nat :=
      if localSteps == 0 then {} else ({} : Std.HashMap String Nat).insert "theorem-rule" localSteps
    let byRule := counts.contextualRules.foldl
      (fun totals rule => totals.insert rule (totals[rule]?.getD 0 + 1)) byRule
    let stats : Stats := ⟨counts.rewrites, counts.sweeps, byRule⟩
    let equivalent := optimized.property.programEquivalent version
    if maxSweeps == 0 then
      ⟨(.Program version optimized.val.1, stats), equivalent⟩
    else
      match Deep.contextualRule optimized.val.1 with
      | none => ⟨(.Program version optimized.val.1, stats), equivalent⟩
      | some shared =>
        let stats : Stats :=
          ⟨counts.rewrites + 1, counts.sweeps, byRule.insert shared.theoremName 1⟩
        let sharing := Deep.TermRel.programEquivalent shared.proof version
        ⟨(.Program version shared.output, stats), fun ctx variant args o =>
          (equivalent ctx variant args o).trans (sharing ctx variant args o)⟩

/-- Optimize a program solely by applying tagged and checked deep rewrite rules. -/
def optimize (program : Program) (maxSweeps : Nat := 12) : Program × Stats :=
  (optimizeWithProof program maxSweeps).val

theorem optimize_preserves (program : Program) (maxSweeps : Nat := 12) :
    Deep.ProgramEquivalent program (optimize program maxSweeps).1 :=
  (optimizeWithProof program maxSweeps).property

end UplcOptimizer
