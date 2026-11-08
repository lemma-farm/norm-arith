-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianKacRice
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianRegressionIsometry
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
set_option autoImplicit false
/-!
# Genuine local coefficient coordinates for every surjective observation

The invertible coefficient block is constructed from the observation's actual
kernel and orthogonal complement. Its persistence on a spatial neighborhood
comes from the openness of invertible continuous linear maps.
-/
@[expose] public section
namespace SlowEquilibration.GaussianLocalCoordinates
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.GaussianRegression
open scoped RealInnerProductSpace ENNReal Topology
noncomputable section
variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace U] [BorelSpace U]
end
end SlowEquilibration.GaussianLocalCoordinates
