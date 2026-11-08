module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.vad256e1f7ac4.SubdiffusiveProcess.Sobolev.WeakGradient
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
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
# The killed Sobolev graph

The zero-boundary space is the closure of the classical function/gradient
pairs of smooth functions compactly supported in the domain. Integration by
parts proves that this closure consists of genuine weak gradients. No trace
or density theorem about a proposed abstract space is assumed.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
end SubdiffusiveProcess
