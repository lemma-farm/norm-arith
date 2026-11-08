-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.VolumeGrowth
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
/-- A single annulus needs one doubling, even when the outer shell is
truncated. BB Lemma 7.5, p. 297. -/
theorem DoublingPatch.weighted_annulus (P : DoublingPatch X) {z : X} (hz : z ∈ P.S)
    {a b : ℝ} (ha : 0 < a) (hb : b ≤ 6 * P.ρ) (hba : b ≤ 2 * a)
    (f : X → ℝ≥0∞) (w : ℝ≥0∞) (hw : ∀ y, a ≤ dist z y → dist z y < b → f y ≤ w) :
    (∫⁻ y in {y | a ≤ dist z y ∧ dist z y < b},
      f y * (volumeAt P.μ z y)⁻¹ ∂P.μ) ≤ w * ENNReal.ofReal P.C_D := by
  by_cases hab : a < b
  · have hv := P.doubling z hz a ha (hab.le.trans hb)
    have hd := (P.doubling z hz b (ha.trans hab) hb).2.2
    have hd' : P.μ (ball z b) ≤ ENNReal.ofReal P.C_D * P.μ (ball z a) :=
      hd.trans (mul_le_mul_right (measure_mono (ball_subset_ball (by linarith : b / 2 ≤ a))) _)
    calc
      _ ≤ ∫⁻ _y in {y | a ≤ dist z y ∧ dist z y < b}, w * (P.μ (ball z a))⁻¹ ∂P.μ := by
        apply setLIntegral_mono measurable_const
        intro y hy
        have hi : (volumeAt P.μ z y)⁻¹ ≤ (P.μ (ball z a))⁻¹ :=
          ENNReal.inv_le_inv.mpr (measure_mono (ball_subset_ball (x := z) hy.1))
        exact (mul_le_mul_left (hw y hy.1 hy.2) _).trans (mul_le_mul_right hi _)
      _ = (w * (P.μ (ball z a))⁻¹) * P.μ {y | a ≤ dist z y ∧ dist z y < b} :=
        setLIntegral_const _ _
      _ ≤ (w * (P.μ (ball z a))⁻¹) * P.μ (ball z b) :=
        mul_le_mul_right (measure_mono (show {y : X | a ≤ dist z y ∧ dist z y < b} ⊆ ball z b from
          fun y hy => by simpa [mem_ball, dist_comm] using hy.2)) _
      _ ≤ (w * (P.μ (ball z a))⁻¹) * (ENNReal.ofReal P.C_D * P.μ (ball z a)) :=
        mul_le_mul_right hd' _
      _ = w * ENNReal.ofReal P.C_D := by
        rw [mul_assoc, mul_left_comm (P.μ (ball z a))⁻¹,
          ENNReal.inv_mul_cancel (ne_of_gt hv.1) (ne_of_lt hv.2.1), mul_one]
  · have he : {y : X | a ≤ dist z y ∧ dist z y < b} = ∅ := by
      ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; intro hy; linarith
    rw [he, setLIntegral_empty]
    positivity
end RothschildStein.H2
