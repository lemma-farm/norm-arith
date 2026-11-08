-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianGlobalKacRice
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.WholeFieldRegression
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.RoundSphereVolume
set_option autoImplicit false
/-!
# Actual mixed tensor field in the genuine round sphere chart

The coordinate gradient is the adjoint derivative of the field's actual
coefficient feature. It is connected to actual first jets, and its covariance
and surjectivity are derived from the actual mixture and chart metric.
-/
@[expose] public section
namespace SlowEquilibration.SphericalChartKacRice
open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphereChartVolume SlowEquilibration.WholeFieldRegression
open SlowEquilibration.GaussianLocalCoordinates
open scoped RealInnerProductSpace ENNReal Topology
noncomputable section
variable {n : ℕ}
end
end SlowEquilibration.SphericalChartKacRice
