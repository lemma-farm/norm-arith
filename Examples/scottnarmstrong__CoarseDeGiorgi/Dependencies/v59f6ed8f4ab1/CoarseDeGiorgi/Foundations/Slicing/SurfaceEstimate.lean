module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Foundations.Slicing.Tonelli
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v59f6ed8f4ab1.CoarseDeGiorgi.Foundations.Slicing.SurfaceGrowth
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Uniform surface-to-bulk estimates before cubical coarea. -/
@[expose] public section
namespace CoarseDeGiorgi.Foundations.Slicing
open Homogenization MeasureTheory Set FracGeometry
open scoped ENNReal
noncomputable section
/-- Integration in the second surface variable uses the uniform exterior tail. -/
theorem averagedKernel_surface_row_le {n : ℕ} (τ : ℝ) {γ r : ℝ}
    (hγ : 0 ≤ γ) (hr : 0 < r) {F : Vec (n + 1) → ℝ} (hF : Measurable F)
    (x : Vec (n + 1)) :
    (∫⁻ y, averagedKernel (2 * (n : ℝ) + 1 + γ) r F (x, y)
      ∂CoarseDeGiorgi.surfaceMeasure τ) ≤
      ENNReal.ofReal (4 * (n + 1 : ℕ) * (2 : ℝ) ^ (2 * (n : ℝ))) *
        ∫⁻ z, Euclid.euclidKernel ((n : ℝ) + 1 + γ) r F (x, z) := by
  rw [lintegral_averagedKernel_row _ _ _ hF x,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro z
  dsimp only
  rw [euclidKernel_eq_product]
  by_cases hxz : x = z
  · subst z
    simp only [differencePower, sub_self, abs_zero, Real.zero_rpow hr.ne',
      ENNReal.ofReal_zero, zero_mul, mul_zero]
    exact le_rfl
  have ht := surface_kernel_tail_le τ x hγ (Euclid.eDist2_pos hxz)
  have h := mul_le_mul_right ht (differencePower r F x z)
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  dsimp only [inversePower]
  ring
end
end CoarseDeGiorgi.Foundations.Slicing
