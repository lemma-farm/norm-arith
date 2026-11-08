-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Section4.Ansatz
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Section4.AdvDiffOp
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Section4.SMat
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Named terms in the Section 5.1 residual identity. -/
@[expose] public section
noncomputable section
open Homogenization
namespace AVenhance.Infra.Section5
open AVenhance
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
end AVenhance.Infra.Section5
end
