module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionLimitPrepared
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.OrthogonalProjectionRadialEstimate
public import Mathlib
set_option autoImplicit false
/-!
# Uniform radial Orlicz bounds for the prepared source approximation

The actual tiny smooth sources retain the distance bound one. Polar rays
are bounded by their orthogonal line integrals; the proved orthogonal
quadratic estimate and the Orlicz product inequality control those line
integrals against the actual singular pin projections. Convolution decreases
Fourier energy, so the resulting constant is independent of the bump index.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
