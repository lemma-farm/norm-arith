/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v45cf8fa1b7f4.DOZZ.Statements.GMC.GmcReferenceMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.gmcRootedMeasure`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- The rooted measure `e^{γ²G(u,·)}M(d·)` appearing in the rooted identity of
[KRV, Corollary 12.2]. -/
noncomputable def gmcRootedMeasure (γ : ℝ) (u : ℂ) (M : Measure ℂ) : Measure ℂ :=
  M.withDensity (fun x => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)))
end DOZZ
