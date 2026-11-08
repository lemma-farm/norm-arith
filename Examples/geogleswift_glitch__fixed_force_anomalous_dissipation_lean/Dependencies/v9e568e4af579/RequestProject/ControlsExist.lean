module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.DampedResponse
/-!
# Lemma 2.13: existence of the controls

The block map is a composition of `4L` elementary shears `p ↦ p ± Y(p)` with `Y ∈ 𝓔` a shear
field.  Concatenating the corresponding autonomous controls `c_k(s) Y_k` on consecutive short
time intervals realizes the block map; four further controls `φ_i'(s) eᵢ` with `∫ φ_i' = 0`
(which do not change the terminal map) cancel the time moments of orders `1, …, M-1`.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
/-! ### Sequential concatenation of shear controls -/
section seq
variable (c : ℕ → ℝ → ℝ) (X : ℕ → Pt 2 → Pt 2) (α : ℕ → ℝ)
variable {c X α} {β : ℕ → ℝ}
end seq
/-! ### The elementary shears -/
end AnomDiss
