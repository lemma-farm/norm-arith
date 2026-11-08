/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3Psi2ChaosOnePotential
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pairings of potentials `y ↦ ∫ h(w) |J(w - y)| dw`

Abstract Tonelli arguments: the integral of `u · Pot h` and of `Pot h₁ · Pot h₂` against `dy`
is bounded in terms of pointwise majorants which are certified by `SingularIntLe` statements.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
/-- The potential `y ↦ ∫ h(w) |J(w - y)| dw`. -/
def i3Psi2Pot (J h : SpaceTime → ℝ) (y : SpaceTime) : ℝ := ∫ w, h w * |J (w - y)|
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
theorem measurable_abs_J_sub {J : SpaceTime → ℝ} (hJm : Measurable J) :
    Measurable (fun p : SpaceTime × SpaceTime => |J (p.1 - p.2)|) :=
  continuous_abs.measurable.comp (hJm.comp (measurable_fst.sub measurable_snd))
/-- `∫ u · Pot h ≤ X`, from a pointwise bound on `∫ u(y) |J(w - y)| dy`. -/
theorem integral_mul_pot_le {J h u H U : SpaceTime → ℝ} {X : ℝ} (hJm : Measurable J)
    (hu0 : ∀ y, 0 ≤ u y) (hum : Measurable u) (hh0 : ∀ w, 0 ≤ h w) (hhm : Measurable h)
    (hhH : ∀ᵐ w : SpaceTime ∂volume, h w ≤ H w)
    (hU : ∀ᵐ w : SpaceTime ∂volume, Integrable (fun y => u y * |J (w - y)|) ∧
      ∫ y, u y * |J (w - y)| ≤ U w)
    (hX : SingularIntLe (fun w => H w * U w) X) :
    Integrable (fun y => u y * i3Psi2Pot J h y) ∧ ∫ y, u y * i3Psi2Pot J h y ≤ X := by
  let G : SpaceTime → SpaceTime → ℝ := fun w y => h w * (u y * |J (w - y)|)
  have hGm : Measurable (Function.uncurry G) := by
    have := measurable_abs_J_sub hJm
    unfold Function.uncurry G
    fun_prop
  have hG0 : ∀ w y, 0 ≤ G w y := fun w y =>
    mul_nonneg (hh0 w) (mul_nonneg (hu0 y) (abs_nonneg _))
  have hGi : ∀ᵐ w : SpaceTime ∂volume, Integrable (G w) := by
    filter_upwards [hU] with w hw
    exact hw.1.const_mul (h w)
  have hint : ∀ w, ∫ y, G w y = h w * ∫ y, u y * |J (w - y)| := fun w => by
    simp only [G]; rw [integral_const_mul]
  have hH : Integrable (fun w => ∫ y, G w y) := by
    refine Integrable.mono' hX.1 (hGm.aestronglyMeasurable.integral_prod_right') ?_
    filter_upwards [hU, hhH] with w hw hH'
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (hG0 w)), hint]
    have n0 : 0 ≤ ∫ y, u y * |J (w - y)| :=
      integral_nonneg fun y => mul_nonneg (hu0 y) (abs_nonneg _)
    exact mul_le_mul hH' hw.2 n0 ((hh0 w).trans hH')
  obtain ⟨_, hmarg, hswap⟩ := integral_swap_nonneg hGm.aestronglyMeasurable hG0 hGi hH
  have e : ∀ y, ∫ w, G w y = u y * i3Psi2Pot J h y := fun y => by
    simp only [G, i3Psi2Pot]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    ring
  simp_rw [e] at hmarg hswap
  refine ⟨hmarg, hswap.trans_le ?_⟩
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
    integral_nonneg (hG0 w)) hX.1 ?_) hX.2
  filter_upwards [hU, hhH] with w hw hH'
  rw [hint]
  have n0 : 0 ≤ ∫ y, u y * |J (w - y)| :=
    integral_nonneg fun y => mul_nonneg (hu0 y) (abs_nonneg _)
  exact mul_le_mul hH' hw.2 n0 ((hh0 w).trans hH')
end RegularityStructures
end
