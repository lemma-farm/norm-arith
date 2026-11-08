module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.Sobolev.DirichletComparison
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
/-! # Continuous responses to actual bounded potentials

The potential-to-coefficient map is the actual exponential L∞ class. The
canonical scalar source and boundary responses satisfy the uniform
multiplicative comparison, hence are continuous and Borel measurable.
This does not supply the model's quantitative resampling or moment bounds.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end SubdiffusiveProcess
