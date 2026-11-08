-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Statements.Ingredients.Ingredients
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `zetaMK` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)
/-- `ζ_{m,k}`, `e.zeta.mk.def` (1246). -/
def zetaMK (m : ℕ) (k : ℤ) : ℝ → ℝ := scaledCutoff I.zeta (tau β I.Λ m) k
end Ingredients
end AVenhance
