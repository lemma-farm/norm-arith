-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Statements.Section3.ChiM
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `psiM` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Homogenization
noncomputable section
namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)
/-- `ψ_m(t, x) := ∑_{k ∈ 2ℤ+1} ζ̂_{m,l_k}(t) ζ_{m,k}(t) ψ_{m,k}(x)`, `e.psi.m` (label 2755). -/
def psiM (m : ℕ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, I.zetaProd m k t * psi β I.Λ m k x
end Ingredients
end AVenhance
