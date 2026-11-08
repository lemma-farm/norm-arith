module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingCellMeasures
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationMassDecomposition
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.SpaceSplittingDistanceBins
public import Mathlib
set_option autoImplicit false
/-! # Actual finite separated-cell carriers for the source distance bins -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical ENNReal
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
