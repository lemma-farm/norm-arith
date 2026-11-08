module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.OrthogonalityKernelUnlinked
public import Mathlib
set_option autoImplicit false
/-! # Actual spatial integration of the unlinked oscillatory kernel -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman
end FalconerThetaGauge
