module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SpaceSplittingNearCells
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedFourierCells
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedFourierArcEnergy
public import Mathlib
set_option autoImplicit false
/-! # Literal occupied-cell expansion and the `81²` near-row Schur bound -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
