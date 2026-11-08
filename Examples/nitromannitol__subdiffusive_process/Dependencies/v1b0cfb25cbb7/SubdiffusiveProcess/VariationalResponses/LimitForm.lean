module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.VariationalResponses.KilledInverse
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v1b0cfb25cbb7.SubdiffusiveProcess.Sobolev.ResponseRecovery
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
open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}
/-- `E(u)` of `eq:mfd-18`:
the dual energy of the killed inverse `G`. -/
def limitFormEnergy (G : DomainL2 Q →L[ℝ] DomainL2 Q) (u : DomainL2 Q) : EReal :=
  ⨆ f : DomainL2 Q, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)
end SubdiffusiveProcess
