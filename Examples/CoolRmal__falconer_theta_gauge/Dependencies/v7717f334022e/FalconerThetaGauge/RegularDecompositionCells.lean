module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.GaugeFrostmanDyadic
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.GaugeSeparatedMeasuresGeometry
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Real
set_option autoImplicit false
/-!
# Actual terminal cells and their original measure weights

The half-open unit square has precisely `4^N` generation-`N` cells. Their
original measure weights partition its mass; this connects finite bottom-up
types to the planar measure in Lemma 5.8.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
