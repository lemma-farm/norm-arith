module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrthogonalProjection
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionOrlicz
public import Mathlib
set_option autoImplicit false
/-!
# Angular shifts of the actual orthogonal density bound

The radial-to-line transfer uses the perpendicular angle. The following exact
periodic change of variables keeps the same arc-length average and identifies
the explicit line density with the true orthogonal pushforward density.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
end FalconerThetaGauge
