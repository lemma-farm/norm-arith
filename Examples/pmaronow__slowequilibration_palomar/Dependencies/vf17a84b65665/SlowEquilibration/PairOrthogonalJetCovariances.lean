-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphericalGaussianJet
set_option autoImplicit false
/-! Actual two-point first-order jet covariances at zero overlap. -/
@[expose] public section
namespace SlowEquilibration.PairOrthogonalJetCovariances
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet
open SphericalAging.FiniteModel SphericalAging.HamiltonianDerivativeCovariance
open scoped BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end
end SlowEquilibration.PairOrthogonalJetCovariances
