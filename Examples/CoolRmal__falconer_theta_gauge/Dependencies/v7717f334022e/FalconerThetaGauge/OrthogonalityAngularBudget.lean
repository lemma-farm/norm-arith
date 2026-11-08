module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.OrthogonalityLinks
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.EqualArcCutoffRegularity
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.MaskedMattilaSymbolScale
public import Mathlib
set_option autoImplicit false
/-! # Actual angular amplitudes and their source orthogonality derivative budget -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
open GaugeFrostman
end FalconerThetaGauge
