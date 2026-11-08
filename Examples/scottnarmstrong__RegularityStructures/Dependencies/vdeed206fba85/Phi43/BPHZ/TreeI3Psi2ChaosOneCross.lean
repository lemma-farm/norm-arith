/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOneLeaves
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOneAbar
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Potential estimates for the regular part `B_z` of the chaos-`1` kernel

With `h_z(w) = |K(-w)| Q(w - z)²`, majorised by `B³ 3^δ s(w)^(-3) s(z - w)^(-(2+δ))` (on the slab
`|t| ≤ 1` carrying the support of `K(-·)`), we bound
`∫ s(z - y)^(-(3+δ')) Pot h_{z'}(y) dy` (the cross term with `Ā`) and
`∫ Pot h_z Pot h_{z'} dy` (the term `B_z B_{z'}`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The weight `h_z(w) = |K(-w)| Q(w - z)²`. -/
def i3Psi2Hz (K Q : SpaceTime → ℝ) (z w : SpaceTime) : ℝ := |K (-w)| * Q (w - z) ^ 2
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
theorem i3Psi2Hz_nonneg (K Q : SpaceTime → ℝ) (z w : SpaceTime) : 0 ≤ i3Psi2Hz K Q z w :=
  mul_nonneg (abs_nonneg _) (sq_nonneg _)
theorem measurable_i3Psi2Hz {K Q : SpaceTime → ℝ} (hKm : Measurable K) (hQm : Measurable Q)
    (z : SpaceTime) : Measurable (i3Psi2Hz K Q z) := by
  unfold i3Psi2Hz
  have := hKm.comp measurable_neg
  have := hQm.comp (measurable_id.sub (measurable_const (a := z)))
  fun_prop
theorem i3Psi2Hz_le {K Q : SpaceTime → ℝ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQe : ∀ x, Q (-x) = Q x) {z : SpaceTime} (hz1 : torusParabolicSize z ≤ 1)
    {w : SpaceTime} (h0 : 0 < torusParabolicSize (0 - w)) (hzw : 0 < torusParabolicSize (z - w)) :
    i3Psi2Hz K Q z w ≤ (B ^ 3 * 3 ^ δ) * (singularPow 3 0 w * singularPow (2 + δ) z w) := by
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hrhs : 0 ≤ (B ^ 3 * 3 ^ δ) * (singularPow 3 0 w * singularPow (2 + δ) z w) :=
    mul_nonneg (mul_nonneg (pow_nonneg hB 3) n3)
      (mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
  by_cases hw : |w.1| ≤ 1
  · have hz1t := abs_fst_le_one_of_size_le_one hz1
    have a1 := hK (-w) (by simpa using h0)
    have a2 : |Q (w - z)| ^ 2 ≤ B ^ 2 * 3 ^ δ * singularPow (2 + δ) z w := by
      rw [Q_sub_comm hQe w z]
      exact abs_Q_sq_le_singularPow_loss hδ hQ hzw (abs_sub_fst_le_four hz1t (hw.trans (by norm_num)))
    have e1 : singularPow 3 0 w = torusParabolicSize (-w) ^ (-(3 : ℝ)) := by simp [singularPow]
    unfold i3Psi2Hz
    rw [← sq_abs (Q (w - z))]
    calc |K (-w)| * |Q (w - z)| ^ 2 ≤ (B * singularPow 3 0 w) *
          (B ^ 2 * 3 ^ δ * singularPow (2 + δ) z w) := by
          rw [e1]
          exact mul_le_mul a1 a2 (sq_nonneg _) (mul_nonneg hB (Real.rpow_nonneg
            (torusParabolicSize_nonneg _) _))
      _ = _ := by ring
  · have : K (-w) = 0 := by
      apply hKs
      have : (-w).1 = -w.1 := rfl
      rw [this, abs_neg]; exact not_le.1 hw
    unfold i3Psi2Hz
    rw [this]
    simpa using hrhs
end RegularityStructures
end
