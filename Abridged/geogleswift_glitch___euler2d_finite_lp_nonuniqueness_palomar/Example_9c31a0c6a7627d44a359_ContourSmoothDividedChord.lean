module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.InnerProductSpace.Calculus

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_9c31a0c6a7627d44a359_ContourSmoothDividedChord ====
/-!
# The genuine smooth extension of a normalized contour chord

The extension is the actual integral of the actual derivative along the
unit segment.  The fundamental theorem of calculus identifies it with
the divided chord away from zero and with the derivative at zero.
-/
@[expose] public section
noncomputable section
open Set Filter Topology Metric MeasureTheory Complex
open scoped ContDiff
namespace Euler2D
def smoothContourNormalizedChord (z : ℝ → ℂ) (θ τ : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, deriv z (θ + u * τ)


set_option linter.unusedVariables false in
theorem norm_smoothContourNormalizedChord_lower {z : ℝ → ℂ} (hz : ContDiff ℝ 1 z) {c : ℝ}
    (hchord : ∀ θ τ : ℝ, |τ| ≤ Real.pi → c * |τ| ≤ ‖z θ - z (θ + τ)‖)
    (θ τ : ℝ) (hτ : |τ| ≤ Real.pi) 
    (h_Euler2D_smul_smoothContourNormalizedChord : ∀ {z : ℝ → ℂ},
      ContDiff ℝ 1 z → ∀ (θ τ : ℝ), τ • Euler2D.smoothContourNormalizedChord z θ τ = z (θ + τ) - z θ)
    (h_Euler2D_norm_hasDerivAt_lower_of_chord : ∀ {z : ℝ → ℂ} {dz : ℂ} {θ c r : ℝ},
      HasDerivAt z dz θ → 0 < r → (∀ (τ : ℝ), |τ| ≤ r → c * |τ| ≤ ‖z θ - z (θ + τ)‖) → c ≤ ‖dz‖)
    (h_Euler2D_smoothContourNormalizedChord_zero : ∀ (z : ℝ → ℂ) (θ : ℝ), Euler2D.smoothContourNormalizedChord z θ 0 = deriv z θ)
    : c ≤ ‖smoothContourNormalizedChord z θ τ‖ := by
  by_cases hzero : τ = 0
  · subst τ
    rw [h_Euler2D_smoothContourNormalizedChord_zero]
    exact h_Euler2D_norm_hasDerivAt_lower_of_chord (hz.differentiable_one θ).hasDerivAt
      Real.pi_pos (hchord θ)
  · have hh := hchord θ τ hτ
    have he : ‖z θ - z (θ + τ)‖ = |τ| * ‖smoothContourNormalizedChord z θ τ‖ := by
      rw [norm_sub_rev, ← h_Euler2D_smul_smoothContourNormalizedChord hz θ τ, norm_smul, Real.norm_eq_abs]
    rw [he, mul_comm c] at hh
    exact le_of_mul_le_mul_left hh (abs_pos.mpr hzero)
end Euler2D
end
