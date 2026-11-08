module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationPassing
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedFourierEnergyReached
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedDistanceEnergyTests
public import Mathlib
set_option autoImplicit false
/-! # The actual shorter passing list holds on every retained fine-cell pair -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
