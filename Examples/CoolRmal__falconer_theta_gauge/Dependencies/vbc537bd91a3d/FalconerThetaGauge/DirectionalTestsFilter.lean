module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.DirectionalTestsRecords
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.FilteredDistanceMeasureFiniteTests
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
