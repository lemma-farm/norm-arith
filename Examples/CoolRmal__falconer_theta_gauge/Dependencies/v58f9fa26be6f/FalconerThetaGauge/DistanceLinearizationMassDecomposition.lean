module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationMassEnergy
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationRetained
public import Mathlib
set_option autoImplicit false
/-! # Actual finite retained cell pairs and their unweighted distance measure decomposition -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
