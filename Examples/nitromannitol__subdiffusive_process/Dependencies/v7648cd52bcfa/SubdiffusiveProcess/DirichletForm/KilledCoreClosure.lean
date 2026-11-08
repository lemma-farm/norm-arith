module
public import Mathlib.Tactic
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7648cd52bcfa.SubdiffusiveProcess.DirichletForm.Killed
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! Deterministic lib data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/
open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
namespace SubdiffusiveProcess.DirichletForm.ClosedForm
noncomputable section
variable {X : Type*} [MeasurableSpace X] {mu : Measure X}
variable [TopologicalSpace X]
end
end SubdiffusiveProcess.DirichletForm.ClosedForm
