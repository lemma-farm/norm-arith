module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.DirectionalTestsMarkov
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularMeasureExcessCount
public import Mathlib
public import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit false
/-! # The actual finite occupied-cell tube count in Definition 6.2 -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman
end FalconerThetaGauge
