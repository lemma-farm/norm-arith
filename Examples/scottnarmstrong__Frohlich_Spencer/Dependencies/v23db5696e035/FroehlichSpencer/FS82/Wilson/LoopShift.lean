/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v23db5696e035.FroehlichSpencer.FS82.Wilson.ShiftProfile
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The explicit loop shift on `ℤ⁴` and its energy

The explicit shift `α` has components along the axes 2 and 3 only,
`α_j(y) = a_{depth(y₀,y₁), j}(y₂, y₃)`, where `depth` is the distance of the column from the
boundary of the sheet and `a_d` is the transverse shift of `ShiftProfile`.

The main result is `loopEnergy_le`: the sum of the squares of the components of `σ - dα`
over any finite box is at most `6 (L + T)`.
-/
public section
namespace FroehlichSpencer.FS82.Wilson
open Finset
@[expose] noncomputable def wallBound₁ (L T : ℕ) (y₀ y₁ : ℤ) : ℝ :=
  if (1 ≤ y₀ ∧ y₀ ≤ (L : ℤ)) ∧ (1 ≤ y₁ ∧ y₁ ≤ ((T - 1 : ℕ) : ℤ)) then
    levelBound (min (y₁ - 1) ((T : ℤ) - 1 - y₁)).toNat
  else 0
theorem wallBound₁_nonneg (L T : ℕ) (y₀ y₁ : ℤ) : 0 ≤ wallBound₁ L T y₀ y₁ := by
  unfold wallBound₁
  split_ifs
  · exact levelBound_nonneg _
  · exact le_rfl
theorem sum_sum_le_sum_range_of_rect (f : ℤ → ℤ → ℝ) (hf : ∀ a b, 0 ≤ f a b) (n m : ℕ)
    (hsupp : ∀ a b, f a b ≠ 0 → (1 ≤ a ∧ a ≤ (n : ℤ)) ∧ (1 ≤ b ∧ b ≤ (m : ℤ)))
    (s t : Finset ℤ) :
    ∑ a ∈ s, ∑ b ∈ t, f a b ≤
      ∑ k ∈ range n, ∑ k' ∈ range m, f ((k : ℤ) + 1) ((k' : ℤ) + 1) := by
  have houter := sum_le_sum_range_of_param (fun a => ∑ b ∈ t, f a b)
    (fun a => sum_nonneg fun b _ => hf a b) n (fun k => (k : ℤ) + 1)
    (by
      intro a ha
      obtain ⟨b, _, hb⟩ := exists_ne_zero_of_sum_ne_zero ha
      have h := (hsupp a b hb).1
      exact ⟨(a - 1).toNat, by omega, by omega⟩) s
  refine houter.trans (sum_le_sum fun k _ => ?_)
  exact sum_le_sum_range_of_param (fun b => f ((k : ℤ) + 1) b) (fun b => hf _ b) m
    (fun k' => (k' : ℤ) + 1)
    (by
      intro b hb
      have h := (hsupp _ b hb).2
      exact ⟨(b - 1).toNat, by omega, by omega⟩) t
theorem sum_wallBound₁_le (L T : ℕ) (s t : Finset ℤ) :
    ∑ y₀ ∈ s, ∑ y₁ ∈ t, wallBound₁ L T y₀ y₁ ≤ 2 * (L : ℝ) := by
  have h := sum_sum_le_sum_range_of_rect (wallBound₁ L T) (wallBound₁_nonneg L T) L (T - 1)
    (by
      intro a b hab
      by_contra hc
      exact hab (by unfold wallBound₁; rw [ite_eq_right hc])) s t
  refine h.trans ?_
  rcases Nat.lt_or_ge T 2 with hT | hT
  · have h0 : T - 1 = 0 := by omega
    rw [h0]
    simp
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 2 := ⟨T - 2, by omega⟩
  have hrange : m + 2 - 1 = m + 1 := by omega
  rw [hrange]
  have hterm : ∀ k ∈ range L, ∀ k' ∈ range (m + 1),
      wallBound₁ L (m + 2) ((k : ℤ) + 1) ((k' : ℤ) + 1) = levelBound (min k' (m - k')) := by
    intro k hk k' hk'
    have hk1 : k < L := mem_range.mp hk
    have hk2 : k' ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hk')
    have hmem : (1 ≤ (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ (L : ℤ)) ∧
        (1 ≤ (k' : ℤ) + 1 ∧ (k' : ℤ) + 1 ≤ ((m + 2 - 1 : ℕ) : ℤ)) := by omega
    have hmin : (min ((k' : ℤ) + 1 - 1) (((m + 2 : ℕ) : ℤ) - 1 - ((k' : ℤ) + 1))).toNat =
        min k' (m - k') := by omega
    unfold wallBound₁
    rw [ite_eq_left hmem, hmin]
  calc ∑ k ∈ range L, ∑ k' ∈ range (m + 1),
        wallBound₁ L (m + 2) ((k : ℤ) + 1) ((k' : ℤ) + 1)
      = ∑ k ∈ range L, ∑ k' ∈ range (m + 1), levelBound (min k' (m - k')) :=
        sum_congr rfl fun k hk => sum_congr rfl fun k' hk' => hterm k hk k' hk'
    _ = (L : ℝ) * ∑ k' ∈ range (m + 1), levelBound (min k' (m - k')) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ (L : ℝ) * 2 := by
        gcongr
        exact tent_levelBound_sum_le m
    _ = 2 * (L : ℝ) := by ring
end FroehlichSpencer.FS82.Wilson
end
