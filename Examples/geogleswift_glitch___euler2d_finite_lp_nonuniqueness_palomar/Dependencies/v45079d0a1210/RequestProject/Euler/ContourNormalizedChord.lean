module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourCauchyRemainderHolder
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourHolderInverseContinuity
/-! # Genuine Hölder normalized chords of a contour

The divided chord is constructed from the actual circle function. Its
Hölder estimates follow from the true derivative and the mean value
theorem, without an integral in the full Hölder space.
-/
@[expose] public section
noncomputable section
open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Euler2D
theorem contour_holderWith_of_norm_bound {γ : ℝ≥0} {C : ℝ} (hC : 0 ≤ C)
    {f : ContourCircle → ℂ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ (γ : ℝ)) :
    HolderWith (⟨C, hC⟩ : ℝ≥0) γ f := by
  change HolderWith (NNReal.mk C hC) γ f
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  have hb : dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ) := by
    simpa only [dist_eq_norm] using hf x y
  exact_mod_cast hb
theorem norm_contourHolder_le_of_bounds {γ : ℝ≥0} (f : ContourHolderSpace γ)
    {C : ℝ} (hC : 0 ≤ C) (hs : ∀ x, ‖f x‖ ≤ C)
    (hh : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ (γ : ℝ)) : ‖f‖ ≤ C :=
  HolderFunctionSpace.norm_le_of_pointwise_holder_bounds f (C := ⟨C, hC⟩) hs
    (contour_holderWith_of_norm_bound hC hh)
end Euler2D
end
