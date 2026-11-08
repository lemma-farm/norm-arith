-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.ConditionedIntrinsicHessian
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.MixtureThresholds
set_option autoImplicit false
/-! # Actual conditioning with the redundant radial score omitted

Value plus complete tangent gradient is nondegenerate for every positive-overlap
finite mixture. In particular this is the proper canonical target for a pure
model, where the radial derivative is a proved multiple of the value.
-/
@[expose] public section
namespace SlowEquilibration.ValueTangentConditioning
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.ConditionedIntrinsicHessian
open SlowEquilibration.SphericalForm SlowEquilibration.SphereHessian
open scoped RealInnerProductSpace ENNReal Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
end
end SlowEquilibration.ValueTangentConditioning
