/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingSpatialKernelFubini
public import Mathlib
set_option autoImplicit false
/-! # Actual absolute-integral bounds for the four-point space-splitting kernel -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped RealInnerProductSpace
namespace FalconerThetaGauge
theorem abs_integral_spaceSplittingJointAmplitude_inner_le_integral_norm
    (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (X X' Y Y' : Set Plane) (K v : ℕ) {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂))
    (hbound₁ : ∀ x w, |b₁ x w| ≤ 1) (hbound₂ : ∀ x w, |b₂ x w| ≤ 1) :
    |∫ z, inner ℝ (spaceSplittingJointAmplitude ρ₁ ρ₂ X Y b₁ b₂ z)
      (spaceSplittingJointAmplitude ρ₁ ρ₂ X' Y' b₁ b₂ z)
      ∂maskedFourierJointMeasure K v| ≤
      ∫ p : (Plane × Plane) × (Plane × Plane),
        ‖spaceSplittingAveragedCircleKernel b₁ b₂ K v p.1.1 p.1.2 p.2.1 p.2.2‖
        ∂((ρ₁.restrict X).prod (ρ₁.restrict X')).prod
          ((ρ₂.restrict Y).prod (ρ₂.restrict Y')) := by
  rw [integral_spaceSplittingJointAmplitude_inner_eq_spatial ρ₁ ρ₂ X X' Y Y' K v
    hb₁ hb₂ hbound₁ hbound₂]
  exact (Complex.abs_re_le_norm _).trans (norm_integral_le_integral_norm _)
end FalconerThetaGauge
