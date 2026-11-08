module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.MaskedFourierPairEnergy
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.OrthogonalityRadialAmplitude
public import Mathlib
set_option autoImplicit false
/-! # The genuine finite radial measure for the dyadic Fourier energy -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
namespace FalconerThetaGauge
/-- The nonnegative radial density appearing in the literal joint square energy. -/
def maskedFourierRadialWeight (K v : ℕ) (r : ℝ) : ℝ :=
  ((2 : ℝ) ^ v)⁻¹ * maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * r ^ 2
theorem maskedFourierRadialWeight_nonneg (K v : ℕ) (r : ℝ) :
    0 ≤ maskedFourierRadialWeight K v r := by
  exact mul_nonneg (mul_nonneg (by positivity)
    (maskedFrequencyCutoff_mem_Icc K _).1) (sq_nonneg _)
theorem integrable_maskedFourierRadialWeight (K v : ℕ) :
    Integrable (maskedFourierRadialWeight K v) := by
  have hb : ∀ r ∈ Icc 0 (4 * (2 : ℝ) ^ v),
      |r ^ (2 : ℕ)| ≤ (4 * (2 : ℝ) ^ v) ^ 2 := by
    intro r hr
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hr.1 hr.2 2
  unfold maskedFourierRadialWeight
  simpa only [mul_assoc, id_eq] using
    (integrable_maskedFrequencyCutoff_mul K v (measurable_id.pow_const 2) hb).const_mul
      (((2 : ℝ) ^ v)⁻¹)
def maskedFourierRadialMeasure (K v : ℕ) : Measure ℝ :=
  volume.withDensity (fun r ↦ ENNReal.ofReal (maskedFourierRadialWeight K v r))
instance isFiniteMeasure_maskedFourierRadialMeasure (K v : ℕ) :
    IsFiniteMeasure (maskedFourierRadialMeasure K v) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_maskedFourierRadialWeight K v)
    (Filter.Eventually.of_forall (maskedFourierRadialWeight_nonneg K v))]
  exact ENNReal.ofReal_ne_top
end FalconerThetaGauge
