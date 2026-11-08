/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2DiagramMultiChaosOnePotBound
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOneSplit
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2DiagramMultiN1
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The regular part of the chaos-`1` kernel, difference

`B^a_z(y) = ∫ K(-w) Q_aa(w - z)² J_a(w - y) dw`.  We have
`B^a_z - B^b_z = ∫ K(-w) (Q_aa² - Q_bb²)(w - z) J_a(w - y) dw + ∫ K(-w) Q_bb(w - z)² ΔJ(w - y) dw`,
so `|B^a_z - B^b_z| ≤ Pot_{J_a}(h^Δ_z) + Pot_{ΔJ}(h^b_z)` with `h^Δ_z = |K(-·)| |Q_aa² - Q_bb²|(· - z)`
and `h^b_z = |K(-·)| Q_bb(· - z)²`.  The weight `h^Δ_z` is majorised by
`μ s(w)^(-3) s(z - w)^(-(2+θ+ν))`.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The weight `h^Δ_z(w) = |K(-w)| |Q_a(w - z)² - Q_b(w - z)²|`. -/
def i3Psi2HzDelta (K Qa Qb : SpaceTime → ℝ) (z w : SpaceTime) : ℝ :=
  |K (-w)| * |Qa (w - z) ^ 2 - Qb (w - z) ^ 2|
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
theorem i3Psi2HzDelta_nonneg (K Qa Qb : SpaceTime → ℝ) (z w : SpaceTime) :
    0 ≤ i3Psi2HzDelta K Qa Qb z w :=
  mul_nonneg (abs_nonneg _) (abs_nonneg _)
theorem measurable_i3Psi2HzDelta {K Qa Qb : SpaceTime → ℝ} (hKm : Measurable K)
    (hQa : Measurable Qa) (hQb : Measurable Qb) (z : SpaceTime) :
    Measurable (i3Psi2HzDelta K Qa Qb z) := by
  unfold i3Psi2HzDelta
  have h1 := hKm.comp measurable_neg
  have h2 := hQa.comp (measurable_id.sub (measurable_const (a := z)))
  have h3 := hQb.comp (measurable_id.sub (measurable_const (a := z)))
  exact (continuous_abs.measurable.comp h1).mul
    (continuous_abs.measurable.comp ((h2.pow_const 2).sub (h3.pow_const 2)))
theorem i3Psi2HzDelta_le {K Qa Qb : SpaceTime → ℝ} {B μ θ ν : ℝ} (hB : 0 ≤ B) (hμ : 0 ≤ μ)
    (hν : 0 ≤ ν) (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQa : ∀ x, 0 < torusParabolicSize x → |Qa x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hQb : ∀ x, 0 < torusParabolicSize x → |Qb x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    (hΔ : ∀ x, 0 < torusParabolicSize x →
      |Qa x - Qb x| ≤ B * μ * torusParabolicSize x ^ (-(1 + θ)))
    (hQae : ∀ x, Qa (-x) = Qa x) (hQbe : ∀ x, Qb (-x) = Qb x) {z : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) {w : SpaceTime} (h0 : 0 < torusParabolicSize (0 - w))
    (hzw : 0 < torusParabolicSize (z - w)) :
    i3Psi2HzDelta K Qa Qb z w ≤
      (2 * B ^ 3 * μ * 3 ^ ν) * (singularPow 3 0 w * singularPow (2 + θ + ν) z w) := by
  have n3 : (0 : ℝ) ≤ 3 ^ ν := Real.rpow_nonneg (by norm_num) _
  have hrhs : 0 ≤ (2 * B ^ 3 * μ * 3 ^ ν) * (singularPow 3 0 w * singularPow (2 + θ + ν) z w) :=
    mul_nonneg (by positivity) (mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
  by_cases hw : |w.1| ≤ 1
  · have hz1t := abs_fst_le_one_of_size_le_one hz1
    have a1 := hK (-w) (by simpa using h0)
    have e1 : singularPow 3 0 w = torusParabolicSize (-w) ^ (-(3 : ℝ)) := by simp [singularPow]
    have h3 := torusParabolicSize_le_three_of_abs_le_four
      (abs_sub_fst_le_four hz1t (hw.trans (by norm_num)))
    have q1 : |Qa (w - z) - Qb (w - z)| ≤ B * μ * singularPow (1 + θ) z w := by
      rw [Q_sub_comm hQae w z, Q_sub_comm hQbe w z]
      exact hΔ _ hzw
    have q2 : |Qa (w - z) + Qb (w - z)| ≤ 2 * B * singularPow 1 z w := by
      rw [Q_sub_comm hQae w z, Q_sub_comm hQbe w z]
      have h1 := abs_add_le (Qa (z - w)) (Qb (z - w))
      have h2 := hQa (z - w) hzw
      have h3 := hQb (z - w) hzw
      unfold singularPow
      linarith
    have mul12 : singularPow (1 + θ) z w * singularPow 1 z w = singularPow (1 + θ + 1) z w :=
      singularPow_mul_self (1 + θ) 1 z w hzw
    have loss := singularPow_loss_le (p := 1 + θ + 1) hν hzw h3
    have q3 : |Qa (w - z) ^ 2 - Qb (w - z) ^ 2| ≤
        2 * B ^ 2 * μ * (3 ^ ν * singularPow (2 + θ + ν) z w) := by
      rw [show Qa (w - z) ^ 2 - Qb (w - z) ^ 2 = (Qa (w - z) - Qb (w - z)) *
        (Qa (w - z) + Qb (w - z)) by ring, abs_mul]
      calc |Qa (w - z) - Qb (w - z)| * |Qa (w - z) + Qb (w - z)|
          ≤ (B * μ * singularPow (1 + θ) z w) * (2 * B * singularPow 1 z w) :=
            mul_le_mul q1 q2 (abs_nonneg _) (mul_nonneg (mul_nonneg hB hμ)
              (singularPow_nonneg _ _ _))
        _ = 2 * B ^ 2 * μ * (singularPow (1 + θ) z w * singularPow 1 z w) := by ring
        _ = 2 * B ^ 2 * μ * singularPow (1 + θ + 1) z w := by rw [mul12]
        _ ≤ 2 * B ^ 2 * μ * (3 ^ ν * singularPow (2 + θ + ν) z w) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have e : 1 + θ + 1 + ν = 2 + θ + ν := by ring
            rw [e] at loss
            exact loss
    unfold i3Psi2HzDelta
    rw [e1] at *
    calc |K (-w)| * |Qa (w - z) ^ 2 - Qb (w - z) ^ 2| ≤
        (B * torusParabolicSize (-w) ^ (-(3 : ℝ))) *
          (2 * B ^ 2 * μ * (3 ^ ν * singularPow (2 + θ + ν) z w)) :=
          mul_le_mul a1 q3 (abs_nonneg _) (mul_nonneg hB (Real.rpow_nonneg
            (torusParabolicSize_nonneg _) _))
      _ = _ := by ring
  · have : K (-w) = 0 := by
      apply hKs
      have : (-w).1 = -w.1 := rfl
      rw [this, abs_neg]; exact not_le.1 hw
    unfold i3Psi2HzDelta
    rw [this]
    simpa using hrhs
end RegularityStructures
end
