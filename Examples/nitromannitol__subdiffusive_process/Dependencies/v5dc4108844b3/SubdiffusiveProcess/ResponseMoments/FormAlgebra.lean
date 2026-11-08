module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v5dc4108844b3.SubdiffusiveProcess.ResponseMoments.Forms
public import Mathlib.Tactic
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
# Bilinearity of a candidate energy measure

The right-hand versions of the two linearity fields of
`SubdiffusiveProcess.ResponseMoments.LocalEnergy`, used throughout Subsection `mfd:sec-compare`
(`mfd:sec-compare`).
-/
open MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
namespace LocalEnergy
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {X : Type*} [MeasurableSpace X]
end LocalEnergy
end ResponseMoments
end SubdiffusiveProcess
