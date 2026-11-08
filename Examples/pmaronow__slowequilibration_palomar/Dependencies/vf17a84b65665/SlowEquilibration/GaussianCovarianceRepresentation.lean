-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianDominatedEdge
public import Mathlib.Analysis.InnerProductSpace.Positive
set_option autoImplicit false
/-! Every genuine centered finite-dimensional Gaussian law with bounded
covariance is an actual linear image of a standard Gaussian with the stated
operator norm. Degenerate covariance is allowed. -/
@[expose] public section
namespace SlowEquilibration.GaussianCovarianceRepresentation
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
end
end SlowEquilibration.GaussianCovarianceRepresentation
