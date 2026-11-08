module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsAverageGridMass
public import Mathlib
set_option autoImplicit false
/-!
# Actual occupied-center counts in dyadic discs

The nine-square cover combines with the genuine occupied-descendant bound
to count the actual centers appearing in the tube test.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
