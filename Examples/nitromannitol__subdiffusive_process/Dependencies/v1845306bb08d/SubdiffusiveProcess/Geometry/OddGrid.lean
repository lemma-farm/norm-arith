module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Centered odd subdivisions of an actual cube

For `2*m+1` children in each coordinate, the middle child is centered on
the original midplane. Triadic grids are specializations of this literal
geometry. Labels are coordinate tuples, not abstract nodes of a tree.
-/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- Coordinate labels in the odd subdivision with `2*m+1` pieces per side. -/
abbrev OddGridIndex (d m : ℕ) := Fin d → Fin (2 * m + 1)
/-- The actual center of a cell, with the middle coordinate label equal to `m`. -/
def oddGridCenter (z : SpatialCoordinates d) (r : ℝ) (m : ℕ)
    (k : OddGridIndex d m) : SpatialCoordinates d :=
  fun i => z i + ((k i).val - (m : ℝ)) * (r / (2 * (m : ℝ) + 1))
/-- The actual open child cube in a centered odd subdivision. -/
def oddGridCell (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (m : ℕ)
    (k : OddGridIndex d m) : Opens (SpatialCoordinates d) :=
  centeredCube (oddGridCenter z r m k) (r / (2 * (m : ℝ) + 1))
    (div_pos hr (by positivity))
/-- Membership is expressed by the literal coordinate endpoints. -/
theorem mem_oddGridCell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m) (x : SpatialCoordinates d) :
    x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)) ↔ ∀ i : Fin d,
      z i + ((k i).val - (m : ℝ)) * (r / (2 * (m : ℝ) + 1)) -
          (r / (2 * (m : ℝ) + 1)) / 2 < x i ∧
      x i < z i + ((k i).val - (m : ℝ)) * (r / (2 * (m : ℝ) + 1)) +
          (r / (2 * (m : ℝ) + 1)) / 2 := by
  change x ∈ (centeredCube (oddGridCenter z r m k) (r / (2 * (m : ℝ) + 1))
    (div_pos hr (by positivity)) : Set (SpatialCoordinates d)) ↔ _
  rw [centeredCube_eq_pi]
  simp only [mem_pi, mem_univ, forall_const, mem_Ioo, oddGridCenter]
theorem oddGridCell_pairwiseDisjoint (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) : Pairwise (fun k l : OddGridIndex d m =>
      Disjoint (oddGridCell z r hr m k : Set (SpatialCoordinates d))
        (oddGridCell z r hr m l : Set (SpatialCoordinates d))) := by
  intro k l hkl
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ l i := by
    contrapose! hkl
    exact funext hkl
  rw [Set.disjoint_left]
  intro x hx hy
  have hk := (mem_oddGridCell z hr m k x).mp hx i
  have hl := (mem_oddGridCell z hr m l x).mp hy i
  let h := r / (2 * (m : ℝ) + 1)
  have hh : 0 < h := div_pos hr (by positivity)
  change z i + ((k i).val - (m : ℝ)) * h - h / 2 < x i ∧
    x i < z i + ((k i).val - (m : ℝ)) * h + h / 2 at hk
  change z i + ((l i).val - (m : ℝ)) * h - h / 2 < x i ∧
    x i < z i + ((l i).val - (m : ℝ)) * h + h / 2 at hl
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · have hstep : ((k i).val : ℝ) + 1 ≤ (l i).val := by
      exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_right hstep hh.le]
  · have hstep : ((l i).val : ℝ) + 1 ≤ (k i).val := by
      exact_mod_cast hlt
    nlinarith [mul_le_mul_of_nonneg_right hstep hh.le]
/-- Extended-real volume of a child is its side length to the dimension. -/
theorem oddGridCell_volume (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m) :
    volume (oddGridCell z r hr m k : Set (SpatialCoordinates d)) =
      ENNReal.ofReal ((r / (2 * (m : ℝ) + 1)) ^ d) :=
  centeredCube_volume _ _
instance oddGridCell_isFiniteMeasure (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m) :
    IsFiniteMeasure (volume.restrict (oddGridCell z r hr m k : Set (SpatialCoordinates d))) :=
  isFiniteMeasure_restrict.mpr (by rw [oddGridCell_volume]; exact ENNReal.ofReal_ne_top)
end SubdiffusiveProcess
