-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Statements.Ingredients.Delta
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `Nstar` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
/-- `e.N` (1018), corrected form: the source's
`N_* := ⌈1/δ² + 500/δ⌉` is enlarged so that every lower bound on `N_*` claimed in
the paper holds by definition: `8 + 4(q-1)(β+γ)/δ` (line 7850, the requirement actually
used), `8 + 128q²/(q-1)` (line 7850) and `8 + 128q²(q-1)` (line 7883), with
`γ = (q-1)β/(q+1)` (`e.gamma`) written out. -/
def Nstar (β : ℝ) : ℕ :=
  ⌈1 / (delta β) ^ 2 + 500 / delta β
      + (8 + 4 * (q β - 1) * (β + (q β - 1) * β / (q β + 1)) / delta β)
      + (8 + 128 * q β ^ 2 / (q β - 1))
      + (8 + 128 * q β ^ 2 * (q β - 1))⌉₊
end AVenhance
