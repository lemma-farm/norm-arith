-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Ingredients.IndIcc
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `scaledCutoff` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
noncomputable section
namespace AVenhance
open Homogenization
/-- `e.zeta.mk.def` (1246), `e.xi.mk.def` (1283): `f_{m,k}(t) = f((t - kτ)/τ)`. -/
def scaledCutoff (f : ℝ → ℝ) (τ : ℝ) (k : ℤ) : ℝ → ℝ := fun t => f ((t - k * τ) / τ)
end AVenhance
