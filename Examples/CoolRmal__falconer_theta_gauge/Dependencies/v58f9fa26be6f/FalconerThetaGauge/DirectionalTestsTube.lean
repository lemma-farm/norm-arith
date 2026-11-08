module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.DirectionalTestsMarkov
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularMeasureExcessCount
public import Mathlib
public import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit false
/-! # The actual finite occupied-cell tube count in Definition 6.2 -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman
/-- The true center of the manuscript's half-open generation-`p` dyadic cell. -/
def dyadicCellCenter (p : ℕ) (k : Fin 2 → ℤ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i ↦ ((k i : ℝ) + 1 / 2) / (2 : ℝ) ^ p)
end FalconerThetaGauge
