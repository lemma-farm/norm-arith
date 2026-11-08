/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.Definitions
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# One-dimensional centered maximal estimates

The fixed-height quadratic `TT*` argument uses a one-dimensional centered
maximal estimate. The covering argument below proves the needed weak estimate
directly from Mathlib's Vitali theorem, with an explicit constant.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace QuadraticCarleson
/-- The weak covering estimate for a bounded family of centered intervals.
Each point of `E` chooses an interval on which the average is at least `a`.
The selected radii need not be measurable, and `E` need not be measurable. -/
theorem centered_average_covering_weak_bound
    (f : ℝ → ℝ≥0∞) (E : Set ℝ) (r : ℝ → ℝ) (R : ℝ)
    (hrpos : ∀ x ∈ E, 0 < r x) (hrbound : ∀ x ∈ E, r x ≤ R)
    (a : ℝ≥0∞)
    (havg : ∀ x ∈ E, a * volume (closedBall x (r x)) ≤
      ∫⁻ y in closedBall x (r x), f y) :
    a * volume E ≤ 4 * ∫⁻ y, f y := by
  obtain ⟨U, hUE, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      E id r R hrbound 4 (by norm_num)
  have hpair : Pairwise (fun i j : U ↦ Disjoint
      (closedBall (i : ℝ) (r i)) (closedBall (j : ℝ) (r j))) := by
    intro i j hij
    exact hdisj i.property j.property (fun h ↦ hij (Subtype.ext h))
  have hpos (i : U) : 0 < volume (closedBall (i : ℝ) (r i)) := by
    rw [Real.volume_closedBall, ENNReal.ofReal_pos]
    exact mul_pos (by norm_num) (hrpos i (hUE i.property))
  have hcount : Countable U := by
    have hh := Measure.countable_meas_pos_of_disjoint_iUnion (μ := (volume : Measure ℝ))
      (fun i : U ↦ measurableSet_closedBall (x := (i : ℝ)) (ε := r i)) hpair
    have hid : {i : U | 0 < volume (closedBall (i : ℝ) (r i))} = univ :=
      Set.eq_univ_of_forall hpos
    rw [hid, Set.countable_univ_iff] at hh
    exact hh
  let : Countable U := hcount
  have hsubset : E ⊆ ⋃ i : U, closedBall (i : ℝ) (4 * r i) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hxy (mem_closedBall_self (hrpos x hx).le)⟩
  have hvolume (i : U) : volume (closedBall (i : ℝ) (4 * r i)) =
      4 * volume (closedBall (i : ℝ) (r i)) := by
    rw [Real.volume_closedBall, Real.volume_closedBall]
    rw [show 2 * (4 * r i) = 4 * (2 * r i) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  calc
    a * volume E ≤ a * ∑' i : U, volume (closedBall (i : ℝ) (4 * r i)) :=
      mul_le_mul' le_rfl ((measure_mono hsubset).trans (measure_iUnion_le _))
    _ = 4 * ∑' i : U, a * volume (closedBall (i : ℝ) (r i)) := by
      simp_rw [hvolume]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      ring
    _ ≤ 4 * ∑' i : U, ∫⁻ y in closedBall (i : ℝ) (r i), f y := by
      gcongr with i
      exact havg i (hUE i.property)
    _ = 4 * ∫⁻ y in ⋃ i : U, closedBall (i : ℝ) (r i), f y := by
      rw [lintegral_iUnion (fun _ ↦ measurableSet_closedBall) hpair]
    _ ≤ 4 * ∫⁻ y, f y := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
/-- The centered interval average, allowing nonnegative extended-valued input. -/
noncomputable def centeredAverage (r : ℝ) (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in closedBall x r, f y) / ENNReal.ofReal (2 * r)
theorem measurable_centeredAverage (r : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (centeredAverage r f) := by
  have hset : MeasurableSet {z : ℝ × ℝ | dist z.2 z.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  have hm : Measurable (fun z : ℝ × ℝ ↦
      {z : ℝ × ℝ | dist z.2 z.1 ≤ r}.indicator (fun z ↦ f z.2) z) :=
    (hf.comp measurable_snd).indicator hset
  have hint := hm.lintegral_prod_right' (ν := (volume : Measure ℝ))
  have hid (x : ℝ) :
      (∫⁻ y, {z : ℝ × ℝ | dist z.2 z.1 ≤ r}.indicator (fun z ↦ f z.2) (x, y)) =
        ∫⁻ y in closedBall x r, f y := by
    rw [← lintegral_indicator measurableSet_closedBall]
    apply lintegral_congr
    intro y
    by_cases hy : dist y x ≤ r <;> simp [Set.indicator, hy, mem_closedBall]
  change Measurable (fun x ↦ (∫⁻ y in closedBall x r, f y) / ENNReal.ofReal (2 * r))
  simpa only [hid] using hint.div_const (ENNReal.ofReal (2 * r))
theorem le_centeredAverage_iff {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ≥0∞) (x : ℝ)
    (a : ℝ≥0∞) : a ≤ centeredAverage r f x ↔
      a * volume (closedBall x r) ≤ ∫⁻ y in closedBall x r, f y := by
  have hd : ENNReal.ofReal (2 * r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  rw [centeredAverage, Real.volume_closedBall]
  exact ENNReal.le_div_iff_mul_le (Or.inl hd) (Or.inl ENNReal.ofReal_ne_top)
/-- Removing values below a threshold changes any centered average by at
most that threshold. -/
theorem centeredAverage_le_truncate_add {r : ℝ} (hr : 0 < r)
    (f : ℝ → ℝ≥0∞) (b : ℝ≥0∞) (x : ℝ) :
    centeredAverage r f x ≤ centeredAverage r ({y | b < f y}.indicator f) x + b := by
  have hden : ENNReal.ofReal (2 * r) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hpoint (y : ℝ) : f y ≤ {y | b < f y}.indicator f y + b := by
    by_cases hy : b < f y
    · simpa [Set.indicator, hy] using (le_add_right le_rfl : f y ≤ f y + b)
    · simpa [Set.indicator, hy] using le_of_not_gt hy
  unfold centeredAverage
  calc
    _ ≤ (∫⁻ y in closedBall x r, {y | b < f y}.indicator f y + b) /
        ENNReal.ofReal (2 * r) :=
      ENNReal.div_le_div_right (lintegral_mono hpoint) _
    _ = ((∫⁻ y in closedBall x r, {y | b < f y}.indicator f y) +
        b * ENNReal.ofReal (2 * r)) / ENNReal.ofReal (2 * r) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ,
        Real.volume_closedBall]
    _ = _ := by
      rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hden ENNReal.ofReal_ne_top]
/-- Integrating the high-value cutoff over all levels gives its exact second
moment. This scalar identity also covers an infinite input value. -/
theorem lintegral_half_level_indicator (v : ℝ≥0∞) :
    (∫⁻ a in Ioi (0 : ℝ), {a : ℝ | ENNReal.ofReal (a / 2) < v}.indicator
      (fun _ ↦ v) a) = 2 * v ^ 2 := by
  have hm : MeasurableSet {a : ℝ | ENNReal.ofReal (a / 2) < v} :=
    measurableSet_lt (measurable_id.div_const 2).ennreal_ofReal measurable_const
  rw [setLIntegral_indicator hm]
  by_cases hv : v = ⊤
  · subst v
    have hs : {a : ℝ | ENNReal.ofReal (a / 2) < ⊤} ∩ Ioi 0 = Ioi 0 := by
      ext a
      simp only [mem_inter_iff, mem_ofPred_eq, ENNReal.ofReal_lt_top, true_and]
    rw [hs]
    simp
  · lift v to ℝ≥0 using hv
    have hs : {a : ℝ | ENNReal.ofReal (a / 2) < (v : ℝ≥0∞)} ∩ Ioi 0 =
        Ioo 0 (2 * (v : ℝ)) := by
      ext a
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨ha, hapos⟩
        have hcmp : a / 2 < (v : ℝ) := by
          rw [← ENNReal.ofReal_coe_nnreal] at ha
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp ha
        exact ⟨hapos, by linarith⟩
      · rintro ⟨hapos, ha⟩
        refine ⟨?_, hapos⟩
        rw [← ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)]
        linarith
    rw [hs, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_coe_nnreal]
    norm_num
    ring
/-- Tonelli converts the integrated localized weak bound into a second moment. -/
theorem lintegral_high_value_tails {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ y,
      {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator f y) = 2 * ∫⁻ y, f y ^ 2 := by
  have hmset : MeasurableSet {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2} :=
    measurableSet_lt (measurable_fst.div_const 2).ennreal_ofReal (hf.comp measurable_snd)
  have hm : Measurable (fun z : ℝ × ℝ ↦
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator (fun z ↦ f z.2) z) :=
    (hf.comp measurable_snd).indicator hmset
  have hswap := lintegral_lintegral_swap
    (f := fun a y : ℝ ↦
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator (fun z ↦ f z.2) (a, y))
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure ℝ)) hm.aemeasurable
  have hid (a y : ℝ) :
      {z : ℝ × ℝ | ENNReal.ofReal (z.1 / 2) < f z.2}.indicator (fun z ↦ f z.2) (a, y) =
      {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator f y := rfl
  simp only [hid] at hswap
  rw [hswap]
  have hid' (y : ℝ) :
      (∫⁻ a in Ioi (0 : ℝ), {y : ℝ | ENNReal.ofReal (a / 2) < f y}.indicator f y) =
        2 * f y ^ 2 := by
    convert lintegral_half_level_indicator (f y) using 1
    apply lintegral_congr
    intro a
    simp [Set.indicator]
  simp_rw [hid']
  exact lintegral_const_mul _ (hf.pow_const 2)
/-- The second-moment layer-cake formula in the normalization used below. -/
theorem lintegral_ofReal_sq_eq_tail {g : ℝ → ℝ} (hg : Measurable g) (hnn : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (g x ^ 2)) =
      ∫⁻ a in Ioi (0 : ℝ), volume {x | a < g x} * ENNReal.ofReal (2 * a) := by
  have hint (t : ℝ) (_ht : 0 < t) : IntervalIntegrable (fun a : ℝ ↦ 2 * a) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hnn' : ∀ᵐ a ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ 2 * a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (by norm_num) ha.le
  have h := lintegral_comp_eq_lintegral_meas_lt_mul volume
    (Filter.Eventually.of_forall hnn) hg.aemeasurable hint hnn'
  have hid (x : ℝ) : (∫ a in 0..g x, 2 * a) = g x ^ 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  simpa only [hid] using h
/-- Increasing finite truncations recover an extended nonnegative square. -/
theorem iSup_min_nat_sq (v : ℝ≥0∞) :
    (⨆ n : ℕ, (min v (n : ℝ≥0∞)) ^ 2) = v ^ 2 := by
  apply le_antisymm
  · apply iSup_le
    intro n
    gcongr
    exact min_le_left _ _
  · by_cases hv : v = ⊤
    · subst v
      simp only [min_top_left, ENNReal.top_pow (by decide : (2 : ℕ) ≠ 0)]
      rw [← ENNReal.iSup_natCast]
      apply iSup_mono
      intro n
      exact_mod_cast (show n ≤ n ^ 2 by nlinarith)
    · obtain ⟨n, hn⟩ := exists_nat_ge v.toReal
      have hvn : v ≤ (n : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hv]
        exact_mod_cast ENNReal.ofReal_le_ofReal hn
      calc
        v ^ 2 = (min v (n : ℝ≥0∞)) ^ 2 := by rw [min_eq_left hvn]
        _ ≤ ⨆ n : ℕ, (min v (n : ℝ≥0∞)) ^ 2 :=
          le_iSup (fun n : ℕ ↦ (min v (n : ℝ≥0∞)) ^ 2) n
end QuadraticCarleson
