module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DistanceLinearizationCollision
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.ScalarEnergyBinningShift
public import Mathlib
set_option autoImplicit false
/-! # Actual one-cell collision mass after distance linearization -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
end FalconerThetaGauge
