-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8c2bc0ddceb.AVenhance.Statements.Ingredients.ScaledCutoff
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `shiftCutoff` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
/-- Translation `f_{m,l} = f_{m,0}(· - l τ''_m)` (1319-1322). -/
def shiftCutoff (f : ℝ → ℝ) (c : ℝ) : ℝ → ℝ := fun t => f (t - c)
end AVenhance
