-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Statements.Ingredients.LIdx
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `psi0` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
/-- `e.def.streamr.0` (1194-1201): `ψ_{0,k}(x) = sin(2π x_i)` if `k ∈ 4ℤ + 2i - 1`,
`i ∈ {1,2}` (coordinates `x 0`, `x 1`), and `0` for even `k`. -/
def psi0 (k : ℤ) (x : Vec 2) : ℝ :=
  if k % 4 = 1 then Real.sin (2 * Real.pi * x 0)
  else if k % 4 = 3 then Real.sin (2 * Real.pi * x 1)
  else 0
end AVenhance
