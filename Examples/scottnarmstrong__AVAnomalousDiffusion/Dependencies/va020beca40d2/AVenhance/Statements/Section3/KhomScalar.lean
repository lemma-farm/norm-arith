-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Section3.Khom
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `KhomScalar` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Homogenization
noncomputable section
namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)
/-- The scalar `a` with `K̄^κ_m = a I` (line 2994): the `(1,1)` entry. That `K̄` is scalar and
`a > 0` is the theorem `Khom_eq_scalar`; the abuse of notation of the source is `KhomScalar`. -/
def KhomScalar (κ : ℝ) (m : ℕ) : ℝ := I.Khom κ m 0 0
end Ingredients
end AVenhance
