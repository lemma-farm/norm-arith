module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.OddGrid
public import Mathlib.MeasureTheory.Measure.Real
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
# The centered odd grid is an actual Lebesgue partition

Containment and disjointness, together with the exact sum of cell volumes,
prove coverage up to Lebesgue null sets. No partition axiom or floor-function
selection is needed. This concerns Lebesgue volume, not limiting energy or
speed measures.
-/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- Volume is additive on every finite subfamily of these actual disjoint cells. -/
theorem oddGrid_subfamily_volume_real (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (S : Finset (OddGridIndex d m)) :
    volume.real (⋃ k ∈ S, (oddGridCell z r hr m k : Set (SpatialCoordinates d))) =
      ∑ k ∈ S, volume.real (oddGridCell z r hr m k : Set (SpatialCoordinates d)) :=
  measureReal_biUnion_finset
    (fun k _ l _ hkl => oddGridCell_pairwiseDisjoint z hr m hkl)
    (fun k _ => (oddGridCell z r hr m k).isOpen.measurableSet)
    (fun k _ => by rw [oddGridCell_volume]; exact ENNReal.ofReal_ne_top)
end SubdiffusiveProcess
