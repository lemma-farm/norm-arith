module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.DirectionalTestsWideningGeometry
public import Mathlib
set_option autoImplicit false
/-! # Quantitative passing-test stability under the actual angular mask thickening -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical ContDiff
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
