-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Flow.IsFlow
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Proofs.Flow.ExistsUniqueFlow
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `existsUnique_flow` (Flow).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open Homogenization
namespace AVenhance
/-- Global well-posedness of the flow for continuous, uniformly globally
Lipschitz fields. -/
theorem existsUnique_flow (b : ℝ → Vec 2 → Vec 2)
    (hb : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hL : ∃ L : ℝ, ∀ t x y, ‖b t x - b t y‖ ≤ L * ‖x - y‖) :
    ∃! X, IsFlow b X := by
  exact AVenhance.Proofs.existsUnique_flow b hb hL
end AVenhance
