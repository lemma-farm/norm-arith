module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.OddGridPartition
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
# The unresolved volume on a centered odd grid

Unresolved labels are precisely those whose actual open cells meet at least
one selected coordinate midplane. Count the middle-coordinate fibers and
use their actual cell volumes. No independence, coefficient estimate, or
assumed geometric remainder enters this argument.
-/
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- Labels whose `i`th coordinate is the middle child. -/
def oddGridPlaneCells (m : ℕ) (i : Fin d) : Finset (OddGridIndex d m) :=
  Finset.univ.filter (fun k => (k i).val = m)
/-- Cells unresolved by the selected coordinate midplanes. -/
def oddGridUnresolved (m : ℕ) (I : Finset (Fin d)) : Finset (OddGridIndex d m) :=
  I.biUnion (oddGridPlaneCells m)
end SubdiffusiveProcess
