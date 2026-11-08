/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.GFFStructure.EquatorRestorationScalar
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.exteriorPinnedKernel`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal
universe u
namespace DOZZ
/-- Exterior-pinned kernel, used for `R > 1`. -/
noncomputable def exteriorPinnedKernel (R : ℝ) (_hR : 0 < R) (x y : ℂ) : ℝ :=
  -Real.log ‖x - y‖ + Real.log (max ‖x‖ R) + Real.log (max ‖y‖ R) - Real.log R
end DOZZ
