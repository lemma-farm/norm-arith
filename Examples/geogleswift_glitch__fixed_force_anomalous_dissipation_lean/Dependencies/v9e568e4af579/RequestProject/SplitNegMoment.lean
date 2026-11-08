module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitRep
/-!
# Ingredients for the negative moment bound of the split maps

An elementary one-sided Lipschitz estimate for `t ↦ t^{-σ}`, the comparison of `|Aᵀe|` for two
Jacobians, the inverse terminal flow map of `b_ω` (built from the block maps), and the negative
moment bound for it inherited from Lemma 2.7.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal Matrix
noncomputable section
namespace AnomDiss
instance isFiniteMeasure_restrict_cell : IsFiniteMeasure (volume.restrict (cell 2)) := by
  rw [isFiniteMeasure_restrict]; simp [cell, Real.volume_Icc_pi]
variable {L M : ℕ} {S : ℕ → ℝ}
end AnomDiss
