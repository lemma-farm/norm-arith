module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionLimitJoint
public import Mathlib
set_option autoImplicit false
/-!
# Weak convergence through separated radial projections

Restriction to a common closed carrier turns continuity on that carrier into
ordinary continuity on a subtype. The resulting weak convergence of the
actual radial joint distributions uses the concrete separation of the pin
and source carriers, so the specified diagonal value has no effect.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
