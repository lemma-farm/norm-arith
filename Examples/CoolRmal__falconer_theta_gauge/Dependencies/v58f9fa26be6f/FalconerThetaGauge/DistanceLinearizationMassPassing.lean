module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationMassProjection
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationPassing
public import Mathlib
set_option autoImplicit false
/-! # The genuine one-cell mass bound from actual passing and the actual profile height -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
