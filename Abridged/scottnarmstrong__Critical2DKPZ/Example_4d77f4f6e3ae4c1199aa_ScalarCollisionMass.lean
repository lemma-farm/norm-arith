module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Set

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vb52d773939f7.Critical2DKPZ.SHF.DeltaBose.ScalarDensity ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
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

noncomputable def scalarIntegrand (θ t u : ℝ) : ℝ :=
  t ^ (u - 1) * Real.exp (θ * u) / Real.Gamma u

/-- The scalar collision density of Tsai (2024), equation (2.4), and Gu–Quastel–Tsai (2021), Lemma 8.4. -/
noncomputable def scalarDensity (θ t : ℝ) : ℝ := ∫ u in Ioi 0, scalarIntegrand θ t u

end Critical2DKPZ.DeltaBose

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_4d77f4f6e3ae4c1199aa_ScalarCollisionMass ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The Laplace transform bounds short-time collision mass by choosing the damping rate at the reciprocal time scale. -/
@[expose] public noncomputable section
open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose
namespace Critical2DKPZ.SHF.Flow
set_option linter.unusedVariables false in
/-- The scalar collision density is integrable on finite positive-time intervals and satisfies its Laplace bound. -/
theorem integral_scalarDensity_Ioo_le_laplace {θ rate v : ℝ}
    (hrate : 0 < rate) (hθ : θ < Real.log rate) 
    (h_Critical2DKPZ_DeltaBose_integrable_scalarDensity_laplace : ∀ {θ rate : ℝ},
      0 < rate →
        θ < Real.log rate →
          MeasureTheory.IntegrableOn
            (fun (t : ℝ) ↦ Real.exp (-(rate * t)) * Critical2DKPZ.DeltaBose.scalarDensity θ t)
            (Set.Ioi 0) MeasureTheory.MeasureSpace.volume)
    (h_Critical2DKPZ_DeltaBose_measurable_scalarDensity : Measurable fun (p : ℝ × ℝ) ↦ Critical2DKPZ.DeltaBose.scalarDensity p.1 p.2)
    (h_Critical2DKPZ_DeltaBose_scalarDensity_pos : ∀ (θ : ℝ) {t : ℝ}, 0 < t → 0 < Critical2DKPZ.DeltaBose.scalarDensity θ t)
    (h_Critical2DKPZ_DeltaBose_integral_scalarDensity_laplace : ∀ {θ rate : ℝ},
      0 < rate →
        θ < Real.log rate →
          ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(rate * t)) * Critical2DKPZ.DeltaBose.scalarDensity θ t =
            (Real.log rate - θ)⁻¹)
    :
    IntegrableOn (scalarDensity θ) (Ioo 0 v) ∧
      (∫ s in Ioo 0 v, scalarDensity θ s) ≤ Real.exp (rate * v) / (Real.log rate - θ) := by
  let F := fun s => Real.exp (-(rate * s)) * scalarDensity θ s
  have hF : IntegrableOn F (Ioi 0) := h_Critical2DKPZ_DeltaBose_integrable_scalarDensity_laplace hrate hθ
  have hpoint (s : ℝ) (hs : s ∈ Ioo 0 v) :
      scalarDensity θ s ≤ Real.exp (rate * v) * F s := by
    have harg : 0 ≤ rate * (v - s) := mul_nonneg hrate.le (sub_nonneg.mpr hs.2.le)
    calc
      scalarDensity θ s ≤ Real.exp (rate * (v - s)) * scalarDensity θ s :=
        le_mul_of_one_le_left (h_Critical2DKPZ_DeltaBose_scalarDensity_pos θ hs.1).le (Real.one_le_exp harg)
      _ = Real.exp (rate * v) * F s := by
        dsimp only [F]
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hsub : Ioo (0 : ℝ) v ⊆ Ioi 0 := Ioo_subset_Ioi_self
  have hbound := (hF.mono_set hsub).const_mul (Real.exp (rate * v))
  have hms : Measurable (scalarDensity θ) := by
    change Measurable (fun s : ℝ => scalarDensity θ s)
    exact h_Critical2DKPZ_DeltaBose_measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hj : IntegrableOn (scalarDensity θ) (Ioo 0 v) := by
    apply hbound.mono' hms.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (h_Critical2DKPZ_DeltaBose_scalarDensity_pos θ hs.1)]
    exact hpoint s hs
  refine ⟨hj, ?_⟩
  calc
    (∫ s in Ioo 0 v, scalarDensity θ s) ≤ ∫ s in Ioo 0 v, Real.exp (rate * v) * F s := by
      apply integral_mono_ae hj hbound
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hpoint s hs
    _ = Real.exp (rate * v) * ∫ s in Ioo 0 v, F s := integral_const_mul _ _
    _ ≤ Real.exp (rate * v) * ∫ s in Ioi 0, F s := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply setIntegral_mono_set hF _ (Eventually.of_forall hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mul_nonneg (Real.exp_nonneg _) (h_Critical2DKPZ_DeltaBose_scalarDensity_pos θ hs).le
    _ = _ := by
      rw [show (∫ s in Ioi 0, F s) = (Real.log rate - θ)⁻¹ from
        h_Critical2DKPZ_DeltaBose_integral_scalarDensity_laplace hrate hθ]
      rfl
end Critical2DKPZ.SHF.Flow
end
