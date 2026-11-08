module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrliczEnergyFourierGaussian
public import Mathlib
set_option autoImplicit false
/-!
# Integrability at the planar Fourier origin

The inverse norm is locally integrable in the plane, with its extended value
infinite at the origin. Its difference from the real inverse occurs at a
Lebesgue-null singleton. This controls the low-frequency part of the actual
logarithmically weighted Fourier energy of a probability measure.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
