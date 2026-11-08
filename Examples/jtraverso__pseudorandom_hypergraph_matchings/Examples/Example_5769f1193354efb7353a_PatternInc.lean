/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__pseudorandom_hypergraph_matchings.Dependencies.vb14578f5b170.PseudorandomLib.PatternAux
public import Mathlib
set_option relaxedAutoImplicit false
/-! # One-step changes of the exposure martingale of a pattern count

Revealing the colour of vertex `i` changes `Xp` by
`∑_{e ∋ i} b_e (𝟙[c(i) = α(rk e i)] - 1/q)` with
`b_e = w e q^{-(ℓ-1-rk e i)} 𝟙[e ∩ [0,i) has pattern α]`. Grouping by `k = rk e i` gives
`∑_e b_e = ∑_{k < ℓ} q^{-(ℓ-1-k)} cnt k (wt ℓ w i) α c`, which is the formula of the paper.
-/
@[expose] public section
namespace Pseudorandom
namespace Patt
open Finset
variable {n q : ℕ} {ℓ : ℕ} {w : Finset (Fin n) → ℝ}
open Classical in
/-- The total coefficient `∑_{e ∋ i} b_e`. -/
noncomputable def incB (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (i : Fin n)
    (c : Fin n → Fin q) : ℝ :=
  ∑ e ∈ (powersetCard ℓ univ).filter (fun e => i ∈ e),
    w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) * if Pat α c (e.filter (· < i)) then 1 else 0)
theorem rk_filter_lt {e : Finset (Fin n)} {i v : Fin n} (hv : v < i) :
    rk (e.filter (· < i)) v = rk e v := by
  unfold rk
  congr 1
  ext x; simp only [mem_filter]
  constructor
  · rintro ⟨⟨hx, -⟩, hxv⟩; exact ⟨hx, hxv⟩
  · rintro ⟨hx, hxv⟩; exact ⟨⟨hx, hxv.trans hv⟩, hxv⟩
theorem cond_iff_pat (α : ℕ → Fin q) (c : Fin n → Fin q) (e : Finset (Fin n)) (i : Fin n) :
    (∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)) ↔ Pat α c (e.filter (· < i)) := by
  unfold Pat
  constructor
  · intro H v hv
    rw [mem_filter] at hv
    rw [rk_filter_lt hv.2]
    exact H v hv.1 hv.2
  · intro H v hv hvi
    have hvi' : v < i := hvi
    have := H v (mem_filter.mpr ⟨hv, hvi'⟩)
    rwa [rk_filter_lt hvi'] at this
theorem card_filter_succ_le {e : Finset (Fin n)} {i : Fin n} (hie : i ∈ e) :
    (e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ))).card = e.card - 1 - rk e i := by
  have h1 := card_filter_add_card_filter_not (s := e) (fun v : Fin n => v < i)
  have h2 : e.filter (fun v : Fin n => ¬ v < i) =
      insert i (e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ))) := by
    ext v
    simp only [mem_filter, mem_insert, not_lt]
    constructor
    · rintro ⟨hv, hiv⟩
      by_cases h : v = i
      · left; exact h
      · right; refine ⟨hv, ?_⟩
        have : (v : ℕ) ≠ i := fun h' => h (Fin.ext h')
        have : (i : ℕ) ≤ v := hiv
        omega
    · rintro (h | ⟨hv, hiv⟩)
      · subst h; exact ⟨hie, le_rfl⟩
      · exact ⟨hv, by rw [Fin.le_def]; omega⟩
  rw [h2, card_insert_of_notMem (by simp)] at h1
  unfold rk
  omega
open Classical in
theorem Xp_inc (α : ℕ → Fin q) (i : Fin n) (c : Fin n → Fin q) (a : Fin q) :
    Xp ℓ w α (i + 1) (Function.update c i a) - Xp ℓ w α i c =
      ∑ e ∈ (powersetCard ℓ univ).filter (fun e => i ∈ e),
        w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) *
          (if Pat α c (e.filter (· < i)) then 1 else 0)) *
          ((if a = α (rk e i) then 1 else 0) - 1 / q) := by
  unfold Xp
  rw [← sum_sub_distrib, sum_filter]
  refine sum_congr rfl fun e he => ?_
  rw [mem_powersetCard] at he
  by_cases hie : i ∈ e
  · rw [if_pos hie]
    have hcard : (e.filter (fun v : Fin n => (i : ℕ) ≤ (v : ℕ))).card =
        (e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ))).card + 1 := by
      have : e.filter (fun v : Fin n => (i : ℕ) ≤ (v : ℕ)) =
          insert i (e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ))) := by
        ext v
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨hv, hiv⟩
          by_cases h : v = i
          · left; exact h
          · right; exact ⟨hv, by have : (v : ℕ) ≠ i := fun h' => h (Fin.ext h'); omega⟩
        · rintro (h | ⟨hv, hiv⟩)
          · subst h; exact ⟨hie, le_rfl⟩
          · exact ⟨hv, by omega⟩
      rw [this, card_insert_of_notMem (by simp)]
    have hcond : (∀ v ∈ e, (v : ℕ) < (i : ℕ) + 1 → Function.update c i a v = α (rk e v)) ↔
        ((∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)) ∧ a = α (rk e i)) := by
      constructor
      · intro H
        refine ⟨fun v hv hvi => ?_, ?_⟩
        · have := H v hv (by omega)
          rwa [Function.update_of_ne (fun h => by subst h; omega)] at this
        · have := H i hie (by omega)
          rwa [Function.update_self] at this
      · rintro ⟨H, ha⟩ v hv hvi
        by_cases h : v = i
        · subst h; rw [Function.update_self]; exact ha
        · rw [Function.update_of_ne h]
          exact H v hv (by have : (v : ℕ) ≠ i := fun h' => h (Fin.ext h'); omega)
    rw [hcard, card_filter_succ_le hie, he.2]
    simp only [hcond, cond_iff_pat]
    by_cases hp : Pat α c (e.filter (· < i))
    · by_cases ha : a = α (rk e i)
      · simp only [hp, ha, and_self, if_true]
        rw [pow_succ]; ring
      · simp only [hp, ha, and_false, if_false, if_true]
        rw [pow_succ]; ring
    · simp [hp]
  · rw [if_neg hie]
    have hfil : e.filter (fun v : Fin n => (i : ℕ) + 1 ≤ (v : ℕ)) =
        e.filter (fun v : Fin n => (i : ℕ) ≤ (v : ℕ)) := by
      refine filter_congr fun v hv => ?_
      have : (v : ℕ) ≠ i := fun h' => hie (by rw [show i = v from Fin.ext h'.symm]; exact hv)
      omega
    have hcond : (∀ v ∈ e, (v : ℕ) < (i : ℕ) + 1 → Function.update c i a v = α (rk e v)) ↔
        (∀ v ∈ e, (v : ℕ) < i → c v = α (rk e v)) := by
      constructor
      · intro H v hv hvi
        have := H v hv (by omega)
        rwa [Function.update_of_ne (fun h => hie (by rw [← h]; exact hv))] at this
      · intro H v hv hvi
        have hne : v ≠ i := fun h => hie (by rw [← h]; exact hv)
        rw [Function.update_of_ne hne]
        exact H v hv (by have : (v : ℕ) ≠ i := fun h' => hne (Fin.ext h'); omega)
    rw [hfil]
    simp only [hcond]
    ring
theorem condAbsInc_Xp_le (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) (α : ℕ → Fin q) (i : Fin n)
    (c : Fin n → Fin q) :
    condAbsInc (unif (Fin n) q) (Xp ℓ w α) i c ≤ 2 / q * incB ℓ w α i c := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold condAbsInc
  simp only [unif]
  simp_rw [Xp_inc α i c]
  calc ∑ a : Fin q, 1 / (q : ℝ) * |∑ e ∈ (powersetCard ℓ univ).filter (fun e => i ∈ e),
          w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) *
          (if Pat α c (e.filter (· < i)) then 1 else 0)) *
          ((if a = α (rk e i) then (1:ℝ) else 0) - 1 / q)|
      ≤ ∑ a : Fin q, 1 / (q : ℝ) * ∑ e ∈ (powersetCard ℓ univ).filter (fun e => i ∈ e),
          w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) *
          (if Pat α c (e.filter (· < i)) then 1 else 0)) *
          |(if a = α (rk e i) then (1:ℝ) else 0) - 1 / q| := by
        refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun e _ => ?_))
        rw [abs_mul, abs_of_nonneg (mul_nonneg (hw e) (mul_nonneg (by positivity)
          (by split_ifs <;> norm_num)))]
    _ = ∑ e ∈ (powersetCard ℓ univ).filter (fun e => i ∈ e),
          w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) *
          (if Pat α c (e.filter (· < i)) then 1 else 0)) *
          ∑ a : Fin q, 1 / (q : ℝ) * |(if a = α (rk e i) then (1:ℝ) else 0) - 1 / q| := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun e _ => sum_congr rfl fun a _ => by ring
    _ ≤ ∑ e ∈ (powersetCard ℓ univ).filter (fun e => i ∈ e),
          w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) *
          (if Pat α c (e.filter (· < i)) then 1 else 0)) * (2 / q) := by
        refine sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (hw e) (mul_nonneg (by positivity) (by split_ifs <;> norm_num)))
        rw [← Finset.add_sum_erase _ _ (mem_univ (α (rk e i)))]
        simp only [if_true]
        have h1 : ∀ a ∈ univ.erase (α (rk e i)),
            1 / (q : ℝ) * |(if a = α (rk e i) then (1:ℝ) else 0) - 1 / q| = 1 / q * (1 / q) := by
          intro a ha
          rw [mem_erase] at ha
          rw [if_neg ha.1, zero_sub, abs_neg, abs_of_pos (by positivity)]
        rw [sum_congr rfl h1, sum_const, card_erase_of_mem (mem_univ _), card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
        rw [abs_of_nonneg (by rw [sub_nonneg, div_le_one hqR]; exact hq1)]
        rw [Nat.cast_sub hq]
        field_simp
        nlinarith
    _ = 2 / q * incB ℓ w α i c := by
        unfold incB
        rw [mul_sum]
        refine sum_congr rfl fun e _ => by ring
end Patt
end Pseudorandom
