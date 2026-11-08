module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsRecords
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.FilteredDistanceMeasureFiniteTests
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
