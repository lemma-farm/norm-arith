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

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v756fe6f4c07b.Critical2DKPZ.Definitions.IsEhrhardType ====
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

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v756fe6f4c07b.Critical2DKPZ.Definitions.LogMGFRatio ====
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
/-- `Φ_F(q) = q⁻¹ log E e^{qF}` for `q ≠ 0` and `E F` for `q = 0` (§3.1). -/
def logMGFRatio {E : Type*} [MeasurableSpace E] (μ : Measure E) (F : E → ℝ) (q : ℝ) : ℝ :=
  if q = 0 then ∫ x, F x ∂μ else q⁻¹ * Real.log (∫ x, Real.exp (q * F x) ∂μ)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_279695bc7f2d2b06ccc4_EhrhardMomentBounds ====
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
/-- Every nonnegative negative-moment order satisfies the sharp quadratic logarithmic bound. -/
theorem log_negative_moment_le {μ : Measure ℝ} (hμ : IsEhrhardType μ)
    (hexp : Integrable (fun x => Real.exp x) μ) {p : ℝ} (hp : 0 ≤ p) 
    (h_Critical2DKPZ_EhrhardType_integrable_exp_mul_of_isEhrhardType : ∀ {μ : MeasureTheory.Measure ℝ},
      Critical2DKPZ.IsEhrhardType μ →
        ∀ {q : ℝ}, q ≤ 0 → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (q * x)) μ)
    (h_Critical2DKPZ_EhrhardType_zero_mem_interior_integrableExpSet_of_isEhrhardType : ∀ {μ : MeasureTheory.Measure ℝ},
      Critical2DKPZ.IsEhrhardType μ →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp x) μ →
          0 ∈ interior (ProbabilityTheory.integrableExpSet id μ))
    (h_Critical2DKPZ_GaussianConvexity_supporting_line_at_zero_on : ∀ {s : Set ℝ} {f : ℝ → ℝ} {d : ℝ},
      ConvexOn ℝ s f → 0 ∈ s → HasDerivAt f d 0 → ∀ {q : ℝ}, q ∈ s → f 0 + d * q ≤ f q)
    (h_Critical2DKPZ_GaussianConvexity_logMGFRatio_id_zero : ∀ (μ : MeasureTheory.Measure ℝ), Critical2DKPZ.logMGFRatio μ id 0 = ∫ (x : ℝ), x ∂μ)
    (h_Critical2DKPZ_GaussianConvexity_convexOn_logMGFRatio_of_isEhrhardType : ∀ {μ : MeasureTheory.Measure ℝ},
      Critical2DKPZ.IsEhrhardType μ →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp x) μ →
          ConvexOn ℝ (ProbabilityTheory.integrableExpSet id μ) (Critical2DKPZ.logMGFRatio μ id))
    (h_Critical2DKPZ_GaussianConvexity_mul_logMGFRatio : ∀ {E : Type} [inst : MeasurableSpace E] (μ : MeasureTheory.Measure E)
      [MeasureTheory.IsProbabilityMeasure μ] (F : E → ℝ) (q : ℝ),
      q * Critical2DKPZ.logMGFRatio μ F q = Real.log (ProbabilityTheory.mgf F μ q))
    (h_Critical2DKPZ_GaussianConvexity_hasDerivAt_logMGFRatio_zero : ∀ {Ω : Type} [inst : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℝ),
      0 ∈ interior (ProbabilityTheory.integrableExpSet X μ) →
        HasDerivAt (Critical2DKPZ.logMGFRatio μ X) (ProbabilityTheory.variance X μ / 2) 0)
    :
    Real.log (∫ x, Real.exp (-p * x) ∂μ) ≤
      -p * (∫ x, x ∂μ) + p ^ 2 / 2 * Var[id; μ] := by
  have := hμ.1
  have h0 := h_Critical2DKPZ_EhrhardType_zero_mem_interior_integrableExpSet_of_isEhrhardType hμ hexp
  have hneg : -p ∈ integrableExpSet id μ :=
    h_Critical2DKPZ_EhrhardType_integrable_exp_mul_of_isEhrhardType hμ (neg_nonpos.mpr hp)
  have hline := h_Critical2DKPZ_GaussianConvexity_supporting_line_at_zero_on (h_Critical2DKPZ_GaussianConvexity_convexOn_logMGFRatio_of_isEhrhardType hμ hexp)
    (interior_subset h0) (h_Critical2DKPZ_GaussianConvexity_hasDerivAt_logMGFRatio_zero μ id h0) hneg
  have hmul := mul_le_mul_of_nonpos_left hline (neg_nonpos.mpr hp)
  rw [h_Critical2DKPZ_GaussianConvexity_mul_logMGFRatio, h_Critical2DKPZ_GaussianConvexity_logMGFRatio_id_zero] at hmul
  change Real.log (mgf id μ (-p)) ≤ _
  calc
    Real.log (mgf id μ (-p)) ≤ -p * ((∫ x, x ∂μ) + Var[id; μ] / 2 * -p) := hmul
    _ = _ := by ring
end Critical2DKPZ.GaussianConvexity
