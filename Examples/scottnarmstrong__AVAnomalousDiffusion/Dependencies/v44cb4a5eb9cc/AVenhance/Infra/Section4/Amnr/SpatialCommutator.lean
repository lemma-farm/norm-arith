-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.TemperatureLaplacian
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Explicit spatial/material commutators used in the temperature cascade. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
/-- Every finite ordered word preserves classical smoothness on an open domain. -/
theorem amnrWord_contDiffOn_infty {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (w : List (Option (Fin 2))) : ContDiffOn ℝ (⊤ : ℕ∞) (amnrWord b w f) U := by
  apply contDiffOn_infty.mpr
  intro N
  exact amnrWord_contDiffOn hU (hb.of_le (by simp)) (hf.of_le (by simp)) w
    (N := N + w.length) (n := N) le_rfl
/-- Primitive velocity gradients are smooth from the velocity itself. -/
theorem amnrVelocityGradient_contDiffOn_infty {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (i p : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (amnrVelocityGradient b i p) U := by
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => b z i) U := (contDiffOn_pi.mp hb) i
  have hg := amnrWord_contDiffOn_infty hU hb hf [some p]
  apply hg.congr
  intro z hz
  exact (amnrOp_space ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) p).symm
end AVenhance.Infra.Section4
