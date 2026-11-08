-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.Memory
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Generic seed multipliers and AMNR seed infrastructure. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
theorem amnr_abs_list_sum_le (L : List ℝ) :
    |L.sum| ≤ (L.map abs).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (abs_add_le a L.sum).trans (add_le_add le_rfl ih)
theorem IsAmnrMixedWord.normalForm {w : List (Option (Fin 2))} (hw : IsAmnrMixedWord w) :
    ∃ α : List (Fin 2), ∃ ℓ : ℕ, w = amnrMixedWord α ℓ := by
  induction w with
  | nil => exact ⟨[], 0, rfl⟩
  | cons d w ih =>
    have hp := List.pairwise_cons.mp hw
    cases d with
    | none =>
      have hall : ∀ a ∈ w, a = none := fun a ha => hp.1 a ha rfl
      have heq := List.eq_replicate_length.mpr hall
      refine ⟨[], w.length + 1, ?_⟩
      simp only [amnrMixedWord, List.map_nil, List.nil_append, List.replicate_succ]
      rw [heq]
      simp only [List.length_replicate]
    | some i =>
      obtain ⟨α, ℓ, hα⟩ := ih hp.2
      exact ⟨i :: α, ℓ, by simp only [amnrMixedWord, List.map_cons, List.cons_append] at *; rw [hα]⟩
end AVenhance.Infra.Section4
