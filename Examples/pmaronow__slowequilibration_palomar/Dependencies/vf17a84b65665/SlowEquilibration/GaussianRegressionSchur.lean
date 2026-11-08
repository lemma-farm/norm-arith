-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianRegressionCovariance
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianOrthogonalRegression
set_option autoImplicit false
/-! Actual residual score covariance and its Schur complement after
conditioning on a genuine finite-dimensional Gaussian observation. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end SlowEquilibration.GaussianRegression
