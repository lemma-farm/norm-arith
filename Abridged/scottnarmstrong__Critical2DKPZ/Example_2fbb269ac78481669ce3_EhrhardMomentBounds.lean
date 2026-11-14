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
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Topology.Order.Basic
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd81972057ac8.Critical2DKPZ.Definitions.IsEhrhardType ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Ehrhard type (§3.3): `X` is constant, or `P(X < a) < 1` for all `a` and
`a ↦ Φ⁻¹(P(X < a))` is concave (with `Φ⁻¹(0) = −∞`), `Φ` the standard Gaussian distribution
function. Stated for the law `μ` of `X`: on `{a : μ(−∞, a) > 0}` (where `Φ⁻¹(μ(−∞,a))` is finite)
`μ(−∞, a) = Φ(g a)` for a concave `g`. -/
def IsEhrhardType (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  ((∃ c, μ = Measure.dirac c) ∨
  ((∀ a, μ (Set.Iio a) < 1) ∧
    ∃ g : ℝ → ℝ, ConcaveOn ℝ {a | 0 < μ (Set.Iio a)} g ∧
      ∀ a, 0 < μ (Set.Iio a) → (μ (Set.Iio a)).toReal = cdf (gaussianReal 0 1) (g a)))
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_2fbb269ac78481669ce3_EhrhardMomentBounds ====
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
/-! Ehrhard-type laws satisfy approximate log-normal moment bounds on their finite exponential-moment domain. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace Critical2DKPZ.GaussianConvexity


set_option linter.unusedVariables false in
/-- The finite second positive moment controls every negative exponential moment. -/
theorem negative_moment_le_second_moment_rpow {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) (hnorm : ∫ x, Real.exp x ∂μ = 1)
    (h2 : Integrable (fun x => Real.exp (2 * x)) μ) {p : ℝ} (hp : 0 ≤ p) 
    (h_Critical2DKPZ_GaussianConvexity_variance_le_neg_two_mean : ∀ {μ : MeasureTheory.Measure ℝ},
      Critical2DKPZ.IsEhrhardType μ →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp x) μ →
          ∫ (x : ℝ), Real.exp x ∂μ = 1 → ProbabilityTheory.variance id μ ≤ -2 * ∫ (x : ℝ), x ∂μ)
    (h_Critical2DKPZ_GaussianConvexity_log_negative_moment_le : ∀ {μ : MeasureTheory.Measure ℝ},
      Critical2DKPZ.IsEhrhardType μ →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp x) μ →
          ∀ {p : ℝ},
            0 ≤ p →
              Real.log (∫ (x : ℝ), Real.exp (-p * x) ∂μ) ≤
                -p * ∫ (x : ℝ), x ∂μ + p ^ 2 / 2 * ProbabilityTheory.variance id μ)
    (h_Critical2DKPZ_EhrhardType_integrable_exp_mul_of_isEhrhardType : ∀ {μ : MeasureTheory.Measure ℝ},
      Critical2DKPZ.IsEhrhardType μ →
        ∀ {q : ℝ}, q ≤ 0 → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (q * x)) μ)
    (h_Critical2DKPZ_GaussianConvexity_neg_mean_le_log_second_moment : ∀ {μ : MeasureTheory.Measure ℝ},
      Critical2DKPZ.IsEhrhardType μ →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp x) μ →
          ∫ (x : ℝ), Real.exp x ∂μ = 1 →
            MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (2 * x)) μ →
              -∫ (x : ℝ), x ∂μ ≤ Real.log (∫ (x : ℝ), Real.exp (2 * x) ∂μ) / 2)
    :
    ∫ x, Real.exp (-p * x) ∂μ ≤
      (∫ x, Real.exp (2 * x) ∂μ) ^ (p * (p + 1) / 2) := by
  have := hμ.1
  have hv := h_Critical2DKPZ_GaussianConvexity_variance_le_neg_two_mean hμ hexp hnorm
  have hm := h_Critical2DKPZ_GaussianConvexity_neg_mean_le_log_second_moment hμ hexp hnorm h2
  have hlog := h_Critical2DKPZ_GaussianConvexity_log_negative_moment_le hμ hexp hp
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  have hfirst : Real.log (∫ x, Real.exp (-p * x) ∂μ) ≤
      (p + p ^ 2) * (-(∫ x, x ∂μ)) := by
    calc
      _ ≤ -p * (∫ x, x ∂μ) + p ^ 2 / 2 * Var[id; μ] := hlog
      _ ≤ -p * (∫ x, x ∂μ) + p ^ 2 / 2 * (-2 * ∫ x, x ∂μ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hv (div_nonneg hp2 (by norm_num))) _
      _ = _ := by ring
  have hlast := hfirst.trans (mul_le_mul_of_nonneg_left hm (add_nonneg hp hp2))
  have hneg := h_Critical2DKPZ_EhrhardType_integrable_exp_mul_of_isEhrhardType hμ (neg_nonpos.mpr hp)
  have hMneg : 0 < ∫ x, Real.exp (-p * x) ∂μ := mgf_pos (X := id) hneg
  have hM2 : 0 < ∫ x, Real.exp (2 * x) ∂μ := mgf_pos (X := id) h2
  rw [Real.rpow_def_of_pos hM2]
  rw [← Real.exp_log hMneg]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (p + p ^ 2) * (Real.log (∫ x, Real.exp (2 * x) ∂μ) / 2) := hlast
    _ = _ := by ring
end Critical2DKPZ.GaussianConvexity
