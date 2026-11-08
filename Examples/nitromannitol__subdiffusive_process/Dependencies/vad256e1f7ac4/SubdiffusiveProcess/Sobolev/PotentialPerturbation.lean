module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.Sobolev.ResponsePerturbation
public import Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.Sobolev.PotentialCoefficient
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! # Local potential changes on the actual Sobolev responses

The coefficient assumptions for relative perturbation are derived from the
actual exponential identity. The constants depend on the changed potential
only, and the support and original local energy are retained.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end SubdiffusiveProcess
