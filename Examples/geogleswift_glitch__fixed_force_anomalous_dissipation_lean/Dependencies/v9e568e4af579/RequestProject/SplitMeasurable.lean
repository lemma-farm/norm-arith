module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitRep
/-!
# Joint continuity (hence measurability) of the canonical split maps

The control coefficients depend continuously on the block parameters, uniformly in time; hence
so do the splitting fields, their flows, and the split maps `Ψ_n`.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
variable {L M : ℕ} {S : ℕ → ℝ}
end AnomDiss
