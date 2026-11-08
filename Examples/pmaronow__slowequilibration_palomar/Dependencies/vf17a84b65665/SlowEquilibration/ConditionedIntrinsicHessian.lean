-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.IntrinsicHessianLaw
set_option autoImplicit false
/-! # Actual Hessian under prescribed whole-field value/radial/gradient conditioning

The canonical full tensor regression version is evaluated at every target.
The true tangent ambient Hessian annihilates the joint observation lift, so
its GOE law survives conditioning. The complete intrinsic Hessian has the
specified radial identity shift.
-/
@[expose] public section
namespace SlowEquilibration.ConditionedIntrinsicHessian
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalForm SlowEquilibration.SphereHessian
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw
open scoped RealInnerProductSpace ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
end
end SlowEquilibration.ConditionedIntrinsicHessian
