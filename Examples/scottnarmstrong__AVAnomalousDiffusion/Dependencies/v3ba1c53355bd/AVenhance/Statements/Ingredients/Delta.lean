-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Ingredients.Q
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `delta` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
/-- `e.delta` (1008): `δ := (1/4)(q-1)(1 - ((2q+1)/(2q+2)) β)`. -/
def delta (β : ℝ) : ℝ :=
  (1 / 4) * (q β - 1) * (1 - ((2 * q β + 1) / (2 * q β + 2)) * β)
end AVenhance
