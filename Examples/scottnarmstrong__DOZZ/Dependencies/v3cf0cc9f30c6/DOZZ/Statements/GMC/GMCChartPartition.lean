/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.GMC.CoulombMass
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.GMCChartPartition`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- A fixed partition of unity between the finite and inverted charts of the sphere. -/
structure GMCChartPartition where
  finiteWeight : BoundedContinuousFunction ℂ ℝ≥0
  infinityWeight : BoundedContinuousFunction ℂ ℝ≥0
  finite_hasCompactSupport : HasCompactSupport (finiteWeight : ℂ → ℝ≥0)
  infinity_hasCompactSupport : HasCompactSupport (infinityWeight : ℂ → ℝ≥0)
  sum_one : ∀ x, x ≠ 0 → finiteWeight x + infinityWeight x⁻¹ = 1
end DOZZ
