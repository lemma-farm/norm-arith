module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.FourierSeparationKernel
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedMattilaSymbolRegularity
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.StationaryCircularSource
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsAverageBands
public import Mathlib
set_option autoImplicit false
/-! # Actual circular pair kernels and their genuine stationary-phase expansion -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff ComplexConjugate RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman
/-- The actual angular integral `I_x(r)` in the far terms of source Estimate 7.8. -/
def spaceSplittingCircleIntegral (b : Plane → UnitCircle → ℝ) (r : ℝ)
    (x x' : Plane) : ℂ :=
  ∫ w, maskedFourierPairKernel b b r w (x, x') ∂circleArcLength
theorem norm_spaceSplittingCircleIntegral_le {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) (hbound : ∀ x w, |b x w| ≤ 1)
    (r : ℝ) (x x' : Plane) : ‖spaceSplittingCircleIntegral b r x x'‖ ≤ 2 * Real.pi := by
  have hi : Integrable (fun w ↦ maskedFourierPairKernel b b r w (x, x'))
      circleArcLength := by
    apply (integrable_const (1 : ℝ)).mono
    · exact ((measurable_maskedFourierPairKernel hb hb r).of_uncurry_right).aestronglyMeasurable
    · filter_upwards [] with w
      rw [norm_maskedFourierPairKernel, norm_one]
      simpa only [one_mul] using
        mul_le_mul (hbound x w) (hbound x' w) (abs_nonneg _) (by norm_num)
  unfold spaceSplittingCircleIntegral
  calc
    _ ≤ ∫ w, ‖maskedFourierPairKernel b b r w (x, x')‖ ∂circleArcLength :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _w, (1 : ℝ) ∂circleArcLength := by
      apply integral_mono hi.norm (integrable_const (1 : ℝ))
      intro w
      dsimp only
      rw [norm_maskedFourierPairKernel]
      simpa only [one_mul] using
        mul_le_mul (hbound x w) (hbound x' w) (abs_nonneg _) (by norm_num)
    _ = _ := by simp [measureReal_def, circleArcLength_univ, Real.pi_pos.le]
end FalconerThetaGauge
