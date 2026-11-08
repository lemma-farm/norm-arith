module
public import Examples.burkh4rt__Discriminative_Kalman_Filter_Formalized.Dependencies.v71a7101e1b81.DiscriminativeKalmanFilter.Assumptions
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter.Proof
variable {d : ℕ}
theorem isProbabilityMeasure_densityMeasure {f : Density d} (hf : IsPDF f) :
    IsProbabilityMeasure (densityMeasure f) := by
  constructor
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf.2.1 hf.1, hf.2.2, ENNReal.ofReal_one]
def densityProbabilityMeasure {f : Density d} (hf : IsPDF f) :
    ProbabilityMeasure (State d) := ⟨densityMeasure f, isProbabilityMeasure_densityMeasure hf⟩
theorem weakly_iff_tendsto {f : ℕ+ → Density d} (hf : ∀ n, IsPDF (f n))
    (P : ProbabilityMeasure (State d)) :
    Weakly f P ↔ Tendsto (fun n => densityProbabilityMeasure (hf n)) atTop (𝓝 P) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  rfl
theorem integral_densityMeasure {f : Density d} (hf : IsPDF f)
    (g : State d → ℝ) :
    (∫ z, g z ∂densityMeasure f) = ∫ z, f z * g z ∂volume := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul₀
    hf.2.1.aemeasurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hf.1] with z hz
  simp [ENNReal.toReal_ofReal hz]
theorem l1Norm_toReal {f : Density d} (hf : AEStronglyMeasurable f volume) :
    (l1Norm f).toReal = ∫ z, ‖f z‖ ∂volume := by
  rw [integral_norm_eq_lintegral_enorm hf]
  simp only [l1Norm, ← ofReal_norm, Real.norm_eq_abs]
theorem bounded_test_integrable {f : Density d} (hf : Integrable f volume)
    (g : BoundedContinuousFunction (State d) ℝ) :
    Integrable (fun z => f z * g z) volume :=
  hf.mul_bdd g.continuous.aestronglyMeasurable (ae_of_all _ g.norm_coe_le_norm)
/-- The estimate used in the first two sentences of the proof of Theorem 2. -/
theorem integral_density_difference_le {f f' : Density d}
    (hf : IsPDF f) (hf' : IsPDF f')
    (g : BoundedContinuousFunction (State d) ℝ) :
    ‖(∫ z, g z ∂densityMeasure f) - (∫ z, g z ∂densityMeasure f')‖ ≤
      ‖g‖ * (l1Distance f f').toReal := by
  rw [integral_densityMeasure hf, integral_densityMeasure hf',
    ← integral_sub (bounded_test_integrable hf.2.1 g)
      (bounded_test_integrable hf'.2.1 g)]
  calc
    _ ≤ ∫ z, ‖g‖ * ‖f z - f' z‖ ∂volume := by
      apply norm_integral_le_of_norm_le ((hf.2.1.sub hf'.2.1).norm.const_mul ‖g‖)
      filter_upwards [] with z
      rw [← sub_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm z) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    _ = ‖g‖ * (l1Distance f f').toReal := by
      rw [integral_const_mul, l1Distance, l1Norm_toReal (hf.2.1.sub hf'.2.1).1]
      rfl
theorem weakly_of_l1Distance {f f' : ℕ+ → Density d} {P : Measure (State d)}
    (hf : ∀ n, IsPDF (f n)) (hf' : ∀ n, IsPDF (f' n))
    (hw : Weakly f P)
    (hl1 : Tendsto (fun n => l1Distance (f n) (f' n)) atTop (𝓝 0)) :
    Weakly f' P := by
  intro g
  have hreal : Tendsto (fun n => (l1Distance (f n) (f' n)).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hl1
  have hdiff : Tendsto (fun n => (∫ z, g z ∂densityMeasure (f n)) -
      (∫ z, g z ∂densityMeasure (f' n))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => integral_density_difference_le (hf n) (hf' n) g)
      (by simpa using hreal.const_mul ‖g‖)
  simpa only [sub_sub_cancel, sub_zero] using (hw g).sub hdiff
end DiscriminativeKalmanFilter.Proof
