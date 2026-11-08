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
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v27b0e38dca4f.Critical2DKPZ.Definitions.Disorder
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v27b0e38dca4f.Critical2DKPZ.Definitions.PointToPoint
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v27b0e38dca4f.Critical2DKPZ.Definitions.Site
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v27b0e38dca4f.Critical2DKPZ.Definitions.SmoothedP2Plane
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v27b0e38dca4f.Critical2DKPZ.Definitions.SrwKernel
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
/-- Smoothed endpoint distribution `μ̂_{m,n}^{(x)}(w) = Z_{m,n}(q_m^{(x)}, w) / Ẑ_{m,n}(x)` (§2.3). -/
def smoothedEndpointDist (β : ℝ) (m n : ℕ) (x : Site) (ω : Disorder) (w : Site) : ℝ :=
  (∑' y : Site, srwKernel m (y - x) * pointToPoint β m (n - m) y w ω) / smoothedP2Plane β m n x ω
end Critical2DKPZ
end
end
