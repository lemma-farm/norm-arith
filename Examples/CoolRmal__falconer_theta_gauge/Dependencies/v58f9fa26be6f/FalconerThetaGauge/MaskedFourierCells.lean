module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.MaskedFourierEnergy
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularMeasureExcessCount
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
