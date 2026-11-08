-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianOrthogonalRegression
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.WholeFieldRegression
set_option autoImplicit false
/-! The genuine canonical Gaussian posterior is invariant under invertible
observation coordinate changes, at every target including null fibers. -/
@[expose] public section
namespace SlowEquilibration.ObservationTargetEquiv
noncomputable section
open Function MeasureTheory ProbabilityTheory
open GaussianRegression SphericalModel WholeFieldRegression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]
end
end SlowEquilibration.ObservationTargetEquiv
