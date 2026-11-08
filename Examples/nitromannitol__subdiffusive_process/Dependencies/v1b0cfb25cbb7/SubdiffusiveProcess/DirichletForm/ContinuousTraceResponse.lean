module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.EnergyMeasureLowerSemicontinuity
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.Sobolev.ContinuousTraceLimit
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! Bounded-energy limits preserve continuous trace-response witnesses.
This module provides the closure step once approximating domain elements and
their uniform limits are constructed; it does not construct those approximants.
-/
open Filter MeasureTheory Set
open scoped Topology ENNReal
noncomputable section
namespace SubdiffusiveProcess.DirichletForm.EnergyMeasure
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable {mu : Measure X} {E : ClosedForm mu}
end SubdiffusiveProcess.DirichletForm.EnergyMeasure
