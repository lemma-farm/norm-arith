-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Roots.IsDivFree
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `IsTestFunction` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Smooth space-periodic test functions on `ℝ × ℝ²`, vanishing for `t ≥ 1`. -/
def IsTestFunction (φ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧
  (∀ t, IsZ2Periodic (φ t)) ∧ ∀ t, 1 ≤ t → ∀ x, φ t x = 0
end AVenhance
