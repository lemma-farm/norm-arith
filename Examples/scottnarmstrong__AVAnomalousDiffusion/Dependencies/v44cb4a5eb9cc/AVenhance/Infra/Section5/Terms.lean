-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Section4.Ansatz
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Section4.AdvDiffOp
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Section4.SMat
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
/-- The flow-pulled gradient `G_l = ∇(T ∘ X_l) ∘ X_l⁻¹`. -/
def G (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (l : ℤ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  spaceGrad (fun y => T t (I.xFlow hΦ m l t y)) (I.xFlowInv hΦ m l t x)
end AVenhance.Infra.Section5
end
