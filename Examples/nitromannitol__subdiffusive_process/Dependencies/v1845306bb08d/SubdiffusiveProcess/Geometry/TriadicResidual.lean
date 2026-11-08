module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1845306bb08d.SubdiffusiveProcess.Geometry.OddGridResidual
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecificLimits.Basic
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
# Vanishing geometric remainder on the actual triadic grid

The odd grid with middle index `3^J / 2` has exactly `3^J` intervals per
coordinate. Its actual unresolved volume fraction is at most `d / 3^J`
and tends to zero. This limit is geometric and deterministic; it is taken
before any cutoff-uniform moment estimate in the reflection argument.
-/
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}
/-- The middle label in a coordinate subdivision of depth `J`. -/
def triadicHalf (J : ℕ) : ℕ := 3 ^ J / 2
end SubdiffusiveProcess
