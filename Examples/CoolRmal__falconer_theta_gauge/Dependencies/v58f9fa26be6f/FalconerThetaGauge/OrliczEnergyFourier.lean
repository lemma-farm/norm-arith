module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrliczEnergyFourierWeight
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrliczEnergyFourierLow
public import Mathlib
set_option autoImplicit false
/-!
# The critical logarithmic Fourier energy estimate

This is the manuscript's Lemma 5.2: the Fourier energy with the literal weight
`log(exp(1) + ‖ξ‖)^γ / ‖ξ‖` is bounded by a constant depending only on γ times
one plus the critical logarithmic spatial energy. The origin and diagonal use
extended nonnegative inverses, and finiteness is proved rather than stipulated.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
