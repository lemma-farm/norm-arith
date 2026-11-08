/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
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
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v4274b53974a7.Critical2DKPZ.Definitions.Disorder
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v4274b53974a7.Critical2DKPZ.Definitions.Site
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
/-- The σ-algebra `ℱ_n = ℱ_{0,n} = σ(ω(j, z) : 0 < j ≤ n)` of the disorder up to time `n`
(§2.1). -/
@[reducible] def disorderPast (n : ℕ) : MeasurableSpace Disorder :=
  MeasurableSpace.comap (fun ω (j : {p : ℕ × Site // 0 < p.1 ∧ p.1 ≤ n}) => ω j) inferInstance
end Critical2DKPZ
end
end
