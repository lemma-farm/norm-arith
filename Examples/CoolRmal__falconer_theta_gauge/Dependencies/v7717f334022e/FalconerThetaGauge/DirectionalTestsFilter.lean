module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.DirectionalTestsRecords
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.FilteredDistanceMeasureFiniteTests
public import Mathlib
set_option autoImplicit false
/-! # The actual finite directional filter made from scheduled tests and occupied cells -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical ContDiff
namespace FalconerThetaGauge
open GaugeFrostman
end FalconerThetaGauge
