module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.FilteredDistanceMeasureFiniteTests
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularDecompositionMeasures
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
