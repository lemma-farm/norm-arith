module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.OrthogonalProjectionSmoothing
public import Mathlib
set_option autoImplicit false
/-!
# Genuine Fourier tails of the concrete density approximants

The residual of the inverse Fourier density and the actual low-pass smoothing
is controlled by the high-frequency tail of the source measure. This supplies
the Plancherel step in the endpoint Orlicz density estimate.
-/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
