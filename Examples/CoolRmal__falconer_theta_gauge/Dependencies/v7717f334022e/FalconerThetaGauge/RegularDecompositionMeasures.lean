module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RegularDecompositionDyadicTypes
public import Mathlib
set_option autoImplicit false
/-!
# Regular probability measures from the actual retained cell types

Depths in the source range from zero to the terminal generation `N`. Regularity
is expressed by pairwise comparison of actual cell masses on that range, which
is equivalent to comparison with the largest occupied cell.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
