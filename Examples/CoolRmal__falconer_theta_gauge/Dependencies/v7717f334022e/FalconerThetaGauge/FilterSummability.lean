module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.Parameters
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.GaugeLogEnergy
public import Mathlib
set_option autoImplicit false
/-!
# Summability of the actual removed-mass errors

All three terms in the scale-dependent filter bound are summable: the rounded
tolerance power, the terminal-scale polynomial times the tolerance exponential,
and the block exponential. No geometric removed-mass estimate is assumed here.
-/
@[expose] public section
noncomputable section
open Filter Asymptotics
namespace FalconerThetaGauge
end FalconerThetaGauge
