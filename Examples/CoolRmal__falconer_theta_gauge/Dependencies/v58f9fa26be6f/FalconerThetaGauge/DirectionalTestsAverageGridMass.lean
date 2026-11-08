module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsAverageGrid
public import Mathlib
set_option autoImplicit false
/-!
# Actual normalized-anchor ball mass

The exact nine-square cover and the genuine regularity estimate control every
closed ball for the normalized restriction to an occupied anchor.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
