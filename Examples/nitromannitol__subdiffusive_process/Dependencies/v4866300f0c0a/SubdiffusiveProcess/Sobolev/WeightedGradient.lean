module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v4866300f0c0a.SubdiffusiveProcess.Sobolev.GradientRange
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
# The finite-cutoff coefficient form on actual gradients

The energy is the sum of the coordinate weighted L2 pairings. Thus it is
exactly the scalar coefficient times the Euclidean dot product of weak
gradients, with no factor 1/2. Positive bounded coefficients and Poincare
on a concrete closed variation space give the actual volume-source equation.
-/
open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end SubdiffusiveProcess
