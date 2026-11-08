module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v8f3676843394.HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The continuous zero extension of a positive-degree Bellman function -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology
/-- Extend the punctured homogeneous function by its forced value zero at the origin. -/
def bellmanOriginExtension (phi : (ℝ × ℝ) → ℝ) (q : ℝ × ℝ) : ℝ :=
  if q = (0, 0) then 0 else phi q
end HypoellipticAleksandrov.KineticAleksandrov
