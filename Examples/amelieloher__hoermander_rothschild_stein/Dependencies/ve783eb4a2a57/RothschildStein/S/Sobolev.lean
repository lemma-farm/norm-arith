-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.S.WeakDeriv
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.memSobolevXLoc
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.ve783eb4a2a57.RothschildStein.Definitions.memSobolevXZero
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {m n : ℕ}
/-- Every letter has positive weight, so weight bounds ordinary length
(BB Def. 1.17, p. 10; Def. 2.2, p. 68). -/
theorem length_le_wordWeight (w : Fin m → ℕ+) (I : List (Fin m)) :
    I.length ≤ wordWeight w I := by
  induction I with
  | nil => simp [wordWeight]
  | cons i I ih =>
    have hi := (w i).pos
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons] at *
    omega
/-- The finite family contains exactly words of weight at most k
(BB Def. 2.2, p. 68). -/
theorem mem_wordFamily_iff (w : Fin m → ℕ+) (k : ℕ) (I : List (Fin m)) :
    I ∈ wordFamily w k ↔ wordWeight w I ≤ k := by
  classical
  unfold wordFamily
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨I.length, Finset.mem_range.mpr (by have := length_le_wordWeight w I; omega), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨fun i => I.get i, Finset.mem_univ _, by simp⟩
/-- The empty word belongs to every weighted family (BB p. 68). -/
theorem nil_mem_wordFamily (w : Fin m → ℕ+) (k : ℕ) : [] ∈ wordFamily w k := by
  simp [mem_wordFamily_iff, wordWeight]
theorem weakWordENorm_eq (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞)
    (f g : (Fin n → ℝ) → ℝ) (hg : hasWeakWordDeriv X Ω I f g) :
    weakWordENorm X Ω I p f = eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  unfold weakWordENorm
  have he : {r | ∃ h : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X Ω I f h ∧
      AEStronglyMeasurable h (volume.restrict (Ω : Set (Fin n → ℝ))) ∧
      r = eLpNorm h p (volume.restrict (Ω : Set (Fin n → ℝ)))} =
      {eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ)))} := by
    ext r
    constructor
    · rintro ⟨h, hh, _, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (eLpNorm_congr_ae (hasWeakWordDeriv_unique X Ω hh hg))
    · intro hr
      exact ⟨g, hg, hg.2.1.aestronglyMeasurable, Set.mem_singleton_iff.mp hr⟩
  rw [he, sInf_singleton]
/-- Deleting letters lowers weight (BB Def. 2.2, p. 68). -/
theorem wordWeight_sublist_le (w : Fin m → ℕ+) {I J : List (Fin m)}
    (h : List.Sublist I J) : wordWeight w I ≤ wordWeight w J := by
  induction h with
  | slnil => simp [wordWeight]
  | cons i h ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons] at *
    omega
  | cons_cons i h ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons] at *
    omega
end RothschildStein.S
