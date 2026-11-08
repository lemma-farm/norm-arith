-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.SigmaMat
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `spaceAvg` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Homogenization
noncomputable section
namespace AVenhance
/-- `⟨f⟩ = ⨍_{𝕋²} f dx` (line 921), as the integral over the open unit cube (`|𝕋²| = 1`). -/
def spaceAvg (f : Vec 2 → ℝ) : ℝ := ∫ x in unitCube, f x
end AVenhance
