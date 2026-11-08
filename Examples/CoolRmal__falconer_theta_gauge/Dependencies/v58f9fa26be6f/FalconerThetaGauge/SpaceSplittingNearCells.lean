module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.OrthogonalityGridCount
public import Mathlib
set_option autoImplicit false
/-! # Exact near-row lattice count in source Estimate 7.8 -/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
def spaceSplittingNear (p : ℕ) (R S : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : Prop :=
  dist (dyadicCellCenter p R.1) (dyadicCellCenter p S.1) ≤ 4 * dyadicRadius p ∧
    dist (dyadicCellCenter p R.2) (dyadicCellCenter p S.2) ≤ 4 * dyadicRadius p
end FalconerThetaGauge
