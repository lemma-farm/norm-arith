module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.OrliczEnergyFourierGaussian
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.OrliczEnergyFourierKernel
public import Mathlib
set_option autoImplicit false
/-!
# Logarithmically weighted Gaussian Fourier energy

The Gaussian Fourier identity is lifted to nonnegative extended integrals.
Tonelli then bounds the logarithmically weighted dyadic frequency series by
the actual spatial critical logarithmic energy.
-/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
