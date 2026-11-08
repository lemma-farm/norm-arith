module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.FilteredDistanceMeasureFiniteTests
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularDecompositionMeasures
public import Mathlib
set_option autoImplicit false
/-!
# The actual regular-decomposition carriers in the filter

The discarded source mass is supplied by the proved dyadic decomposition,
including its rounded parameters and original half-open cell carriers.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace FalconerThetaGauge
open GaugeSeparatedMeasures
end FalconerThetaGauge
