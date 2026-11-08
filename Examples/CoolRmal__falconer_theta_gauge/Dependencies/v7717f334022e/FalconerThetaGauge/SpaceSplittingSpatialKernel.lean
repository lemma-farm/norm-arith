/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SpaceSplittingCircle
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SpaceSplittingNearSchur
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.OrthogonalityKernelCrossBound
public import Mathlib
set_option autoImplicit false
/-! # The literal four-point averaged circular kernel for space splitting -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped RealInnerProductSpace
namespace FalconerThetaGauge
/-- The actual averaged product of the two masked circular integrals. -/
def spaceSplittingAveragedCircleKernel (b₁ b₂ : Plane → UnitCircle → ℝ) (K v : ℕ)
    (x x' y y' : Plane) : ℂ :=
  (((2 : ℝ) ^ v : ℝ) : ℂ)⁻¹ * ∫ r in Ioi 0,
    ((maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ 2 : ℝ) : ℂ) *
      spaceSplittingCircleIntegral b₁ r x x' * spaceSplittingCircleIntegral b₂ r y y'
theorem spaceSplittingAveragedCircleKernel_eq_radial (b₁ b₂ : Plane → UnitCircle → ℝ)
    (K v : ℕ) (x x' y y' : Plane) :
    spaceSplittingAveragedCircleKernel b₁ b₂ K v x x' y y' =
      ∫ r, spaceSplittingCircleIntegral b₁ r x x' *
        spaceSplittingCircleIntegral b₂ r y y' ∂maskedFourierRadialMeasure K v := by
  rw [spaceSplittingAveragedCircleKernel, ← integral_const_mul,
    integral_maskedFourierRadialMeasure]
  simp only [Complex.real_smul, maskedFourierRadialWeight, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_assoc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hzero := maskedFourierRadialWeight_eq_zero_of_nonpos K v (le_of_not_gt hr)
  have he := congrArg Complex.ofReal hzero
  simp only [maskedFourierRadialWeight, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_zero] at he
  simp only [← mul_assoc, he, zero_mul]
@[fun_prop]
theorem measurable_maskedFourierPairKernel_joint {b₁ b₂ : Plane → UnitCircle → ℝ}
    (hb₁ : Measurable (uncurry b₁)) (hb₂ : Measurable (uncurry b₂)) :
    Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦
      maskedFourierPairKernel b₁ b₂ q.2.1 q.2.2 q.1) := by
  have h₁ : Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦ b₁ q.1.1 q.2.2) :=
    hb₁.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  have h₂ : Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦ b₂ q.1.2 q.2.2) :=
    hb₂.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  simp only [maskedFourierPairKernel]
  exact ((by fun_prop : Measurable (fun q : (Plane × Plane) × (ℝ × UnitCircle) ↦
    Complex.exp (-((q.2.1 * inner ℝ (q.1.1 - q.1.2) (q.2.2 : Plane) : ℝ) : ℂ) *
      Complex.I))).mul h₁.complex_ofReal).mul h₂.complex_ofReal
@[fun_prop]
theorem measurable_spaceSplittingCircleIntegral_joint {b : Plane → UnitCircle → ℝ}
    (hb : Measurable (uncurry b)) :
    Measurable (fun q : (Plane × Plane) × ℝ ↦
      spaceSplittingCircleIntegral b q.2 q.1.1 q.1.2) := by
  have hm : Measurable (fun q : ((Plane × Plane) × ℝ) × UnitCircle ↦
      maskedFourierPairKernel b b q.1.2 q.2 q.1.1) :=
    (measurable_maskedFourierPairKernel_joint hb hb).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
end FalconerThetaGauge
