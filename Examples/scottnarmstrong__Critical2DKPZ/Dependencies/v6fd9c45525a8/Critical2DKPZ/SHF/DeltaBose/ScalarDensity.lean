/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v6fd9c45525a8.Critical2DKPZ.SHF.DeltaBose.GammaBounds
import Mathlib
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The Gamma-integral collision density in Tsai’s equation (2.4) and Gu–Quastel–Tsai’s Lemma 8.4 is positive and jointly continuous at positive times and satisfies an exact scaling identity. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped Topology
namespace Critical2DKPZ.DeltaBose
/-- The Laplace variable form of the scalar collision integrand. -/
noncomputable def gammaLaplaceIntegrand (s u : ℝ) : ℝ := Real.exp (s * u) / Real.Gamma u
/-- Nonnegativity on the integration domain. -/
theorem gammaLaplaceIntegrand_pos (s : ℝ) {u : ℝ} (hu : 0 < u) :
    0 < gammaLaplaceIntegrand s u :=
  div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hu)
/-- The Gamma-Laplace integrand has an integrable majorant uniform over every half-line of parameters bounded above. -/
theorem gammaLaplaceIntegrand_le {s B r u : ℝ} (hs : s ≤ B) (hu : 0 < u) :
    gammaLaplaceIntegrand s u ≤
      Real.exp (Real.exp (B + r) + 1) * (u * Real.exp (-(r * u))) := by
  have h := inv_gamma_le_exp_mul hu (Real.exp_pos (B + r))
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
  unfold gammaLaplaceIntegrand
  rw [div_eq_mul_inv]
  calc Real.exp (s * u) * (Real.Gamma u)⁻¹
      ≤ Real.exp (s * u) * (Real.exp (Real.exp (B + r) + 1) * u *
          Real.exp ((B + r) * -u)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = Real.exp (Real.exp (B + r) + 1) * u *
          Real.exp ((s - B - r) * u) := by
      have he : Real.exp ((s - B - r) * u) =
          Real.exp (s * u) * Real.exp ((B + r) * -u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ Real.exp (Real.exp (B + r) + 1) * u * Real.exp (-(r * u)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hs) hu.le]
      · positivity
    _ = _ := mul_assoc _ _ _
/-- Absolute convergence of the scalar Gamma integral in Laplace variables. -/
theorem integrableOn_gammaLaplaceIntegrand (s : ℝ) :
    IntegrableOn (gammaLaplaceIntegrand s) (Ioi 0) := by
  apply ((integrableOn_mul_exp_neg (r := 1) zero_lt_one).const_mul
    (Real.exp (Real.exp (s + 1) + 1))).mono'
  · apply ContinuousOn.aestronglyMeasurable
    · apply ContinuousOn.div
      · fun_prop
      · exact Real.differentiableOn_Gamma_Ioi.continuousOn
      · intro u hu
        exact (Real.Gamma_pos_of_pos hu).ne'
    · exact measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (gammaLaplaceIntegrand_pos s hu)]
    exact gammaLaplaceIntegrand_le le_rfl hu
noncomputable def scalarIntegrand (θ t u : ℝ) : ℝ :=
  t ^ (u - 1) * Real.exp (θ * u) / Real.Gamma u
/-- Factoring out the time identifies the natural Laplace parameter. -/
theorem scalarIntegrand_eq {t : ℝ} (ht : 0 < t) (θ u : ℝ) :
    scalarIntegrand θ t u = t⁻¹ * gammaLaplaceIntegrand (θ + Real.log t) u := by
  unfold scalarIntegrand gammaLaplaceIntegrand
  rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  rw [Real.rpow_def_of_pos ht]
  rw [show (θ + Real.log t) * u = Real.log t * u + θ * u by ring, Real.exp_add]
  ring
/-- The scalar collision density of Tsai (2024), equation (2.4), and Gu–Quastel–Tsai (2021), Lemma 8.4. -/
noncomputable def scalarDensity (θ t : ℝ) : ℝ := ∫ u in Ioi 0, scalarIntegrand θ t u
theorem scalarDensity_eq_laplace (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    scalarDensity θ t = t⁻¹ * ∫ u in Ioi 0, gammaLaplaceIntegrand (θ + Real.log t) u := by
  unfold scalarDensity
  simp_rw [scalarIntegrand_eq ht]
  exact integral_const_mul _ _
/-- Strict positivity at every positive time. -/
theorem scalarDensity_pos (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < scalarDensity θ t := by
  rw [scalarDensity_eq_laplace θ ht]
  apply mul_pos (inv_pos.mpr ht)
  have hs : Function.support (gammaLaplaceIntegrand (θ + Real.log t)) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro u hu
    exact (gammaLaplaceIntegrand_pos _ hu).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (gammaLaplaceIntegrand_pos _ hu).le
  · exact integrableOn_gammaLaplaceIntegrand _
end Critical2DKPZ.DeltaBose
