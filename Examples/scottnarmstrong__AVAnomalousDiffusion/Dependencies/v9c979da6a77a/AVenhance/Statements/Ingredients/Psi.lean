-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Ingredients.Psi0
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `psi` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
/-- `e.def.streamr` (1207-1210): `ψ_{m,k} := a_m ε_m² ψ_{0,k}(· / ε_m)`, `m ≥ 1`. -/
def psi (β : ℝ) (Λ : ℕ) (m : ℕ) (k : ℤ) (x : Vec 2) : ℝ :=
  a β Λ m * epsilon β Λ m ^ 2 * psi0 k ((epsilon β Λ m)⁻¹ • x)
end AVenhance
