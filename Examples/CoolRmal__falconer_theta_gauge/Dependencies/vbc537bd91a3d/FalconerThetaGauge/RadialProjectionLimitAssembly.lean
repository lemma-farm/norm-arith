module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RadialProjectionLimitEndpoint
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RadialProjectionLimitConvergence
public import Mathlib
set_option autoImplicit false
/-!
# Passage from smooth radial bounds to the actual radial endpoint

The approximating source measures are actual Lebesgue densities. Their exact
polar ray densities satisfy a stronger uniform moment bound; source weak
convergence and separation identify their joint limit with the original
radial pushforward. This yields its actual almost-everywhere density and the
requested lower moment.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
