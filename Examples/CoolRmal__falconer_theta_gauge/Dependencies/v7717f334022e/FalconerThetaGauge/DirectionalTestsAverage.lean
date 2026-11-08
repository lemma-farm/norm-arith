module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.DirectionalTestsAverageTubeBound
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.DirectionalTestsMaskSupport
public import Mathlib
set_option autoImplicit false
/-! # Lemma 6.5 with the actual scale-dependent parameter facts -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
