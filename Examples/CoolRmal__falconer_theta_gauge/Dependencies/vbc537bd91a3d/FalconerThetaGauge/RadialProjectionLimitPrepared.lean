module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RadialProjectionLimitSmoothing
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.GaugeSeparatedMeasuresGeometry
public import Mathlib
set_option autoImplicit false
/-!
# Separated carriers for the endpoint approximation

These concrete bounds use the actual preparation radii. Pins lie in a ball
of radius `1/400`, source smoothing lies in a ball of radius `1/80`, and their
centers are a quarter unit apart. Thus every approximating pair stays at
distance at least `1/5` and at most one.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
