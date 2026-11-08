module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RadialProjectionRay
public import Mathlib
set_option autoImplicit false
/-!
# Actual orthogonal densities and the radial full-line identity

In an orthonormal Cartesian frame, integrating a planar density along the second
coordinate gives the density of its actual first-coordinate orthogonal pushforward.
The identity holds pointwise along every fiber, so it can be used with singular
pin measures. These arguments adapt `FalconerPacking.RadialProjectionLine`
(original source credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/RadialProjectionLine.lean
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
end FalconerThetaGauge
