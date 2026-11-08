module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.Sobolev.ResponseSpace
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! # Actual local energies of coordinate gradients

Localization acts on L2 gradients, not on Sobolev functions: multiplying a
function by an indicator would introduce a distributional boundary term.
The local energy below is exactly the coefficient-weighted set integral.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end SubdiffusiveProcess
