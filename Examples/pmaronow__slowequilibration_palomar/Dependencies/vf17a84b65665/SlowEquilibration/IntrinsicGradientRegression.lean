-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphereHessian
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.JointFieldRegression
set_option autoImplicit false
/-!
# Canonical regression at the actual intrinsic spherical gradient

The observation takes values in the complete tangent plane, with the ambient
Euclidean inner product. Its covariance, nondegeneracy, and full original-tensor
zero-target law are derived from the actual mixed field. Chart conditioning
agrees pointwise at zero with this coordinate-free law.
-/
@[expose] public section
namespace SlowEquilibration.IntrinsicGradientRegression
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.SphereHessian
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace ENNReal Topology
noncomputable section
end
end SlowEquilibration.IntrinsicGradientRegression
