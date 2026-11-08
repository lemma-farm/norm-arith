module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationMass
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsProjection
public import Mathlib
set_option autoImplicit false
/-! # Exact normalization of the one-cell projection and distance masses -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
