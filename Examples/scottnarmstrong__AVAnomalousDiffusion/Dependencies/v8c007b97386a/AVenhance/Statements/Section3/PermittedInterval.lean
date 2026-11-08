-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.KappaAt
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `permittedInterval` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Homogenization
noncomputable section
namespace AVenhance
/-- `e.permitted` (label 3564): the interval `[½ ε_M^{2β/(q+1)}, 2 ε_M^{2β/(q+1)}]`. -/
def permittedInterval (β : ℝ) (Λ : ℕ) (M : ℕ) : Set ℝ :=
  Set.Icc (1 / 2 * epsilon β Λ M ^ (2 * β / (q β + 1)))
    (2 * epsilon β Λ M ^ (2 * β / (q β + 1)))
end AVenhance
