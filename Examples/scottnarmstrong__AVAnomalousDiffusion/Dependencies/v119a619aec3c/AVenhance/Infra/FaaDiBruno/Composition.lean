-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.Resummation
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Sharp composition bounds

The analytic composition estimate is proved from the ordered-finpartition
Faà di Bruno formula, keeping the paper's coordinate seminorms and constants.
-/
@[expose] public section
noncomputable section
namespace AVenhance.FaaDiBruno
open MeasureTheory
open Homogenization
local instance realMeasureSpace : MeasureSpace ℝ := Real.measureSpace
end AVenhance.FaaDiBruno
end
