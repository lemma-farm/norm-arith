import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyCrossScaleCorrelation
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual cross pairings of the separated quadratic pieces

The mixed integral composition is justified on `L¹` inputs using the
bounded finite-range kernels. The resulting cross-pairing estimate keeps
the two actual central-third restricted input masses.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
set_option autoImplicit false
namespace FiniteRangeKernel
end FiniteRangeKernel
/-- The actual positive quadratic convolution as a bounded finite-range
kernel, with its proved cutoff constant and support radius. -/
noncomputable def krauseLaceyPositiveKernel (j : ℤ) : FiniteRangeKernel where
  toFun x t := annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t)
  measurable_toFun := by
    have ha : Continuous (positiveDyadicAmplitude j) :=
      continuous_iff_continuousAt.mpr
        (fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt)
    unfold annularQuadraticKernel phase
    fun_prop
  radius := (2 : ℝ) ^ (j - 1)
  radius_pos := by positivity
  bound := positiveDyadicAmplitudeBound / (2 : ℝ) ^ (j - 1)
  bound_nonneg := div_nonneg positiveDyadicAmplitudeBound_nonneg (by positivity)
  norm_le x t := by
    simp only [annularQuadraticKernel, norm_mul, norm_phase, mul_one]
    exact norm_positiveDyadicAmplitude_le j (x - t)
  eq_zero x t ht := by
    have hz : positiveDyadicAmplitude j (x - t) = 0 := by
      by_contra hn
      have hs := positiveDyadicAmplitude_support_subset j hn
      have hnonneg : 0 ≤ x - t := (by positivity : 0 ≤ (2 : ℝ) ^ (j - 1) / 4).trans hs.1
      rw [abs_of_nonneg hnonneg] at ht
      exact (not_lt_of_ge hs.2) ht
    simp [annularQuadraticKernel, hz]
@[simp] theorem krauseLaceyPositiveKernel_apply (j : ℤ) (x t : ℝ) :
    krauseLaceyPositiveKernel j x t =
      annularQuadraticKernel (positiveDyadicAmplitude j) 1 (x - t) := rfl
end QuadraticCarleson
