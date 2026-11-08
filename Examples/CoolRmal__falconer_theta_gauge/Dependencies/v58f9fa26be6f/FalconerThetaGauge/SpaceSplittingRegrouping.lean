module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingKernelEnergy
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ScheduledStateEnergies
public import Mathlib
set_option autoImplicit false
/-! # The actual separated-cell weighted kernel sums obey the source `2⁹⁰` bound -/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
