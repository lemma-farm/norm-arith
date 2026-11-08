module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingWeightedKernel
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingSeparatedPartners
public import Mathlib
set_option autoImplicit false
/-! # The actual weighted space-splitting kernel is controlled by the actual source energies -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
