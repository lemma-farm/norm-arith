module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RadialProjectionUniformBound
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RadialProjectionLimitAssembly
public import Mathlib
set_option autoImplicit false
/-!
# Actual radial endpoint for the gauge Frostman preparation

The genuine prepared source measures have logarithmic energies at every
order. A bound two logarithmic powers stronger than the requested order
gives uniform absolute continuity of their joint smooth radial distributions.
The proved weak-limit argument yields the actual circle pushforward density,
including its finite requested Orlicz moment, almost everywhere in the pin.
This route uses no additional hypothesis on the target compact set.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
