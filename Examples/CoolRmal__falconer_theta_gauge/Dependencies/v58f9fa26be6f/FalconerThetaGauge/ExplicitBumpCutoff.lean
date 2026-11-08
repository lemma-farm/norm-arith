module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ExplicitBumpScale
public import Mathlib
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Haar.Unique
set_option autoImplicit false
/-! # Actual smooth masks from closed neighborhoods of arbitrary passing sets -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff Convolution
namespace FalconerThetaGauge
theorem contDiff_iteratedDeriv_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2
/-- A true real-line convolution mask, including masks of periodic sets. -/
def smoothIndicator (K : ℕ) (δ : ℝ) (S : Set ℝ) : ℝ → ℝ :=
  S.indicator (fun _ ↦ 1) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] scaledExplicitBump K δ
theorem locallyIntegrable_indicator_one {S : Set ℝ} (hS : MeasurableSet S) :
    LocallyIntegrable (S.indicator (fun _ ↦ (1 : ℝ))) volume :=
  (continuous_const.locallyIntegrable).indicator hS
theorem contDiff_smoothIndicator (K : ℕ) {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : MeasurableSet S) : ContDiff ℝ ∞ (smoothIndicator K δ S) :=
  (hasCompactSupport_scaledExplicitBump K hδ).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_indicator_one hS)
    (contDiff_scaledExplicitBump K δ)
theorem iteratedDeriv_smoothIndicator (K k : ℕ) {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    iteratedDeriv k (smoothIndicator K δ S) =
      S.indicator (fun _ ↦ 1) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        iteratedDeriv k (scaledExplicitBump K δ) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, smoothIndicator]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    ext x
    exact ((hasCompactSupport_iteratedDeriv k
      (hasCompactSupport_scaledExplicitBump K hδ)).hasDerivAt_convolution_right
        (ContinuousLinearMap.mul ℝ ℝ)
        (locallyIntegrable_indicator_one hS)
        ((contDiff_iteratedDeriv_infty (contDiff_scaledExplicitBump K δ) k).of_le (by simp))
        x).deriv
theorem norm_iteratedDeriv_smoothIndicator_le (K k : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {S : Set ℝ} (hS : MeasurableSet S) (x : ℝ) :
    ‖iteratedDeriv k (smoothIndicator K δ S) x‖ ≤
      ∫ t : ℝ, ‖iteratedDeriv k (scaledExplicitBump K δ) t‖ := by
  rw [iteratedDeriv_smoothIndicator K k hδ hS, convolution_def]
  have hk := hasCompactSupport_iteratedDeriv k (hasCompactSupport_scaledExplicitBump K hδ)
  have hc := (contDiff_iteratedDeriv_infty (contDiff_scaledExplicitBump K δ) k).continuous
  have hi := (hk.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_indicator_one hS) hc x).integrable
  have hn : Integrable (fun t : ℝ ↦ ‖iteratedDeriv k (scaledExplicitBump K δ) (x - t)‖) :=
    (integrable_comp_sub_left (μ := (volume : Measure ℝ)) _ x).mpr
      (hc.integrable_of_hasCompactSupport hk).norm
  calc
    _ ≤ ∫ t : ℝ, ‖(ContinuousLinearMap.mul ℝ ℝ (S.indicator (fun _ ↦ 1) t))
        (iteratedDeriv k (scaledExplicitBump K δ) (x - t))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖iteratedDeriv k (scaledExplicitBump K δ) (x - t)‖ := by
      apply integral_mono hi.norm hn
      intro t
      by_cases ht : t ∈ S <;> simp [ContinuousLinearMap.mul_apply', ht]
    _ = _ := integral_sub_left_eq_self
      (fun t : ℝ ↦ ‖iteratedDeriv k (scaledExplicitBump K δ) t‖) volume x
theorem norm_iteratedDeriv_smoothIndicator_le_explicit (K k : ℕ) (hk : k ≤ K)
    {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ} (hS : MeasurableSet S) (x : ℝ) :
    ‖iteratedDeriv k (smoothIndicator K δ S) x‖ ≤
      δ⁻¹ ^ k * ((Real.pi ^ 2 / 6) ^ k * (k.factorial : ℝ) ^ 2) :=
  (norm_iteratedDeriv_smoothIndicator_le K k hδ hS x).trans
    (integral_norm_iteratedDeriv_scaledExplicitBump_le K k hk hδ)
theorem smoothIndicator_nonneg (K : ℕ) {δ : ℝ} (hδ : 0 < δ) (S : Set ℝ) (x : ℝ) :
    0 ≤ smoothIndicator K δ S x := by
  rw [smoothIndicator, convolution_def]
  apply integral_nonneg
  intro t
  change 0 ≤ S.indicator (fun _ ↦ 1) t * scaledExplicitBump K δ (x - t)
  exact mul_nonneg (by by_cases ht : t ∈ S <;> simp [ht])
    (scaledExplicitBump_nonneg K hδ _)
theorem smoothIndicator_le_one (K : ℕ) {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : MeasurableSet S) (x : ℝ) : smoothIndicator K δ S x ≤ 1 := by
  have h := norm_iteratedDeriv_smoothIndicator_le_explicit K 0 (Nat.zero_le K) hδ hS x
  simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow,
    mul_one] at h
  exact (le_abs_self _).trans h
end FalconerThetaGauge
