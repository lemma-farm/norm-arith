module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.OrthogonalityLinks
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.EqualArcCutoffRegularity
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.MaskedMattilaSymbolScale
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
