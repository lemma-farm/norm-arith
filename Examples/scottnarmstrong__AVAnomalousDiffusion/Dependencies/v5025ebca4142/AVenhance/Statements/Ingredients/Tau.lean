-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v5025ebca4142.AVenhance.Statements.Ingredients.TauP
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `tau` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
/-- `e.taum.def` (1108-1116): `τ_0 := 1`, and for `m ≥ 1`,
`τ_m := (4⌈ε_{m-1}^{-δ}⌉ + 1)⁻² τ''_m`. -/
def tau (β : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  if m = 0 then 1
  else (4 * ((⌈epsilon β Λ (m - 1) ^ (-delta β)⌉₊ : ℕ) : ℝ) + 1)⁻¹ ^ 2 * tauPP β Λ m
end AVenhance
