module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.AffineDirichletPositivity
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.AffineUpperBounds
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Sobolev.MeanZeroRepresentative
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# The concrete diagonal response defect

The equal-slope defect used in Theorem 19 is the sum of the actual affine
Dirichlet and inverse-Neumann responses, divided by twice the domain volume,
minus the squared slope. Nonnegativity follows by using the mean-subtracted
Dirichlet minimizer in the Neumann problem. The upper bound is independent
of the domain volume, as required to remove unresolved subcubes at a fixed
cutoff. No matrix representation or subadditivity is assumed here.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
def affineDiagonalDefect
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (_hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) : ℝ :=
  (affineDirichletResponse hΩ hD a p + affineInverseNeumannResponse hN a p) /
    (2 * volume.real (Ω : Set (SpatialCoordinates d))) - ∑ i : Fin d, (p i)^2
theorem affineDiagonalDefect_le_of_unit_slope
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) {p : Fin d → ℝ} (hp : ∑ i : Fin d, (p i)^2 = 1)
    {c M : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a.val x)
    (hM : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ M) :
    affineDiagonalDefect hΩ hvol hD hN a p ≤ (M + c⁻¹) / 2 - 1 := by
  have hd := affineDirichletResponse_le_upper_bound hΩ hD a p hM
  have hn := affineInverseNeumannResponse_le_lower_bound hN a p hc ha
  rw [hp, one_mul] at hd hn
  unfold affineDiagonalDefect
  rw [hp, sub_le_sub_iff_right, div_le_iff₀ (mul_pos (by norm_num) hvol)]
  nlinarith
end SubdiffusiveProcess
