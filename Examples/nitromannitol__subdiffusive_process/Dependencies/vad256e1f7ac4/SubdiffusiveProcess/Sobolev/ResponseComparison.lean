module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.Sobolev.ResponseSpace
public import Mathlib.Analysis.SpecialFunctions.Exp
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
# Canonical inverse responses: coefficient order and potential comparison

Coefficient order is reversed for inverse responses. Scalar homogeneity and
the attained variational formula prove the exact exponential comparison used
by the finite-band compactness argument. These are actual responses on the
concrete Sobolev spaces; no comparison property is assumed of the response.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end SubdiffusiveProcess
