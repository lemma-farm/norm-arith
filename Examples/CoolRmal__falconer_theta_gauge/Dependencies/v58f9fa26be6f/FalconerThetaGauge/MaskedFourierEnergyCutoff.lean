module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpCutoff
public import Mathlib
set_option autoImplicit false
/-! # The genuine smooth dyadic-frequency cutoff of the source -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ContDiff Convolution
namespace FalconerThetaGauge
/-- The actual source cutoff `1_[3/8,3] * ω_(1/8)`. -/
def maskedFrequencyCutoff (K : ℕ) : ℝ → ℝ :=
  smoothIndicator K (1 / 8) (Icc (3 / 8) 3)
theorem contDiff_maskedFrequencyCutoff (K : ℕ) :
    ContDiff ℝ ∞ (maskedFrequencyCutoff K) :=
  contDiff_smoothIndicator K (by norm_num) measurableSet_Icc
theorem maskedFrequencyCutoff_mem_Icc (K : ℕ) (x : ℝ) :
    maskedFrequencyCutoff K x ∈ Icc 0 1 :=
  ⟨smoothIndicator_nonneg K (by norm_num) _ x,
    smoothIndicator_le_one K (by norm_num) measurableSet_Icc x⟩
theorem maskedFrequencyCutoff_eq_zero (K : ℕ) {x : ℝ} (hx : x ∉ Icc (1 / 4) 4) :
    maskedFrequencyCutoff K x = 0 := by
  rw [maskedFrequencyCutoff, smoothIndicator, convolution_eq_swap]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  by_cases ht : 1 / 8 < |t|
  · simp only [ContinuousLinearMap.mul_apply',
      scaledExplicitBump_eq_zero_of_scale_lt_abs K (by norm_num) ht, mul_zero, Pi.zero_apply]
  · have ht' := abs_le.mp (le_of_not_gt ht)
    have hnot : x - t ∉ Icc (3 / 8 : ℝ) 3 := by
      intro hmem
      apply hx
      constructor <;> linarith [hmem.1, hmem.2, ht'.1, ht'.2]
    simp only [ContinuousLinearMap.mul_apply', indicator_of_notMem hnot, zero_mul, Pi.zero_apply]
theorem integrable_maskedFrequencyCutoff_mul (K v : ℕ) {f : ℝ → ℝ}
    (hf : Measurable f) {B : ℝ}
    (hB : ∀ r ∈ Icc 0 (4 * (2 : ℝ) ^ v), |f r| ≤ B) :
    Integrable (fun r ↦ maskedFrequencyCutoff K (r / (2 : ℝ) ^ v) * f r) := by
  have hs : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  have hBi : Integrable ((Icc 0 (4 * (2 : ℝ) ^ v)).indicator (fun _ ↦ B)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  apply hBi.mono ?_ ?_
  · exact (((contDiff_maskedFrequencyCutoff K).continuous.measurable.comp
      (measurable_id.div_const _)).mul hf).aestronglyMeasurable
  · filter_upwards [] with r
    by_cases hr : r ∈ Icc 0 (4 * (2 : ℝ) ^ v)
    · rw [indicator_of_mem hr, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (maskedFrequencyCutoff_mem_Icc K _).1]
      exact (mul_le_mul_of_nonneg_right (maskedFrequencyCutoff_mem_Icc K _).2
        (abs_nonneg _)).trans (by simpa using (hB r hr).trans (le_abs_self B))
    · have hnot : r / (2 : ℝ) ^ v ∉ Icc (1 / 4) 4 := by
        intro hmem
        apply hr
        constructor
        · have := (le_div_iff₀ hs).1 hmem.1
          linarith
        · exact (div_le_iff₀ hs).1 hmem.2
      simp [maskedFrequencyCutoff_eq_zero K hnot, indicator_of_notMem hr]
end FalconerThetaGauge
