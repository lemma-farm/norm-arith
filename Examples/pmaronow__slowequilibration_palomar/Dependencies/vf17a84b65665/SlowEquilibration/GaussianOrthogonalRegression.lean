-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianRegressionDensity
set_option autoImplicit false
/-! Sequential regression of orthogonal Gaussian observations, for arbitrary
nonnegative Borel marks of the entire coefficient vector. The identity holds
at the literal zero target, not merely for almost every observation. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H]
end
end SlowEquilibration.GaussianRegression
