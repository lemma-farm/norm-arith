module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionLine
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrliczDuality
public import Mathlib
set_option autoImplicit false
/-!
# Extended Orlicz transfer for actual radial densities

The extended functions agree with the manuscript's real functions on finite
nonnegative arguments and take the value infinity at infinity. This preserves
monotonicity when a positive-ray density is not yet known finite. The radial
transfer then applies directly to the literal circle pushforward densities.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
end FalconerThetaGauge
