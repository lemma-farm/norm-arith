module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.All
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.DirichletForm.FOTProduct
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
/-! # Local energy lower semicontinuity

This module constructs a closed form by adding a nonnegative local energy penalty
and uses it to pass uniform local energy-measure bounds to bounded-energy `L²`
limits. It does not assert convergence of the energy measures.
-/
open Filter MeasureTheory Set Topology
noncomputable section
namespace SubdiffusiveProcess.DirichletForm.EnergyMeasure
end SubdiffusiveProcess.DirichletForm.EnergyMeasure
