module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.NonstationaryPhaseUniform
public import Mathlib
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
set_option autoImplicit false
/-!
# Nonstationary integration by parts over a period

The endpoint terms cancel for genuine periodic amplitudes and phases. The
same transported amplitudes and their local support derivative bounds are
therefore available for the circle integrals used in the energy estimates.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ContDiff
namespace FalconerThetaGauge
end FalconerThetaGauge
