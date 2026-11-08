module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.MaskedFourierEnergy
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RegularMeasureExcessCount
public import Mathlib
set_option autoImplicit false
/-! # The actual Fourier amplitudes split over occupied dyadic descendants -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
