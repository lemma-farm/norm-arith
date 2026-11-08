/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v18751a2484e5.DOZZ.Statements.Defs.CircleSelfEnergy
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.circleEnergyGap`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- Log-energy `∬ G d(f dx − σ) d(f dx − σ)` of the signed measure `f dx − σ_{x,r}`. -/
noncomputable def circleEnergyGap (x : ℂ) (r : ℝ) (f : TestFn) : ℝ :=
  gffCov f f - 2 * circleCross x r f + circleSelfEnergy x r
end DOZZ
