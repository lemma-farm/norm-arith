/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularMeasureExcessGauge
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularDecompositionMeasures
public import Mathlib
set_option autoImplicit false
/-!
# Actual excess properties and occupied-cell counts of retained parts

The normalized retained carriers satisfy Lemma 5.10, and their occupied
descendants satisfy the counting estimate (5.2).
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman GaugeSeparatedMeasures
theorem measurableSet_unitSquare : MeasurableSet unitSquare := by
  rw [← biUnion_unitCellIndices 0]
  exact measurableSet_cellUnion 0 _
def occupiedCellDescendants (ρ : Measure Plane) (g p : ℕ) (q : Fin 2 → ℤ) :
    Finset (Fin 2 → ℤ) :=
  (unitCellIndices p).filter
    (fun k ↦ ancestor (p - g) k = q ∧ 0 < unitCellWeight ρ p k)
end FalconerThetaGauge
