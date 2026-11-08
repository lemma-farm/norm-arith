/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.RandomWalk.Port.Walk.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The one-dimensional lazy random walk kernel

The kernel `p_m(k) = 4^{-m} binom(2m,m+k)` describes a walk that stays put with
probability one half and moves in each direction with probability one quarter. It is
symmetric and unimodal, has total mass one, and its maximum is at most `(m+1)^{-1/2}`. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
/-! ### Binomial coefficients with an integer lower index -/
/-- `binom n j` for an integer `j`, extended by `0` to `j < 0`.  `Nat.choose`
already vanishes for `j > n`. -/
noncomputable def binomZ (n : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (n.choose j.toNat : ℝ) else 0
lemma binomZ_of_neg {n : ℕ} {j : ℤ} (h : j < 0) : binomZ n j = 0 := by
  unfold binomZ; rw [ite_eq_right (by omega)]
/-- At a nonnegative integer lower index, the extended binomial coefficient equals the usual binomial coefficient. -/
lemma binomZ_natCast (n j : ℕ) : binomZ n (j : ℤ) = (n.choose j : ℝ) := by
  unfold binomZ; rw [ite_eq_left (by positivity)]; simp
lemma binomZ_succ (n : ℕ) (j : ℤ) : binomZ (n + 1) j = binomZ n (j - 1) + binomZ n j := by
  rcases lt_trichotomy j 0 with h | h | h
  · rw [binomZ_of_neg h, binomZ_of_neg (by omega), binomZ_of_neg h]; ring
  · subst h
    rw [binomZ_of_neg (by norm_num : (0 : ℤ) - 1 < 0),
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num, binomZ_natCast, binomZ_natCast]
    simp
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℕ) + 1 := ⟨(j - 1).toNat, by omega⟩
    have h1 : ((t : ℤ) + 1) - 1 = (t : ℤ) := by ring
    have h2 : ((t : ℤ) + 1) = ((t + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, h2, binomZ_natCast, binomZ_natCast, binomZ_natCast]
    rw [Nat.choose_succ_succ]
    push_cast; ring
lemma binomZ_le_middle (m : ℕ) (j : ℤ) : binomZ (2 * m) j ≤ binomZ (2 * m) (m : ℤ) := by
  have hmid : binomZ (2 * m) (m : ℤ) = ((2 * m).choose m : ℝ) := binomZ_natCast _ _
  rcases lt_or_ge j 0 with h | h
  · rw [binomZ_of_neg h, hmid]; positivity
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℤ) := ⟨j.toNat, by omega⟩
    rw [binomZ_natCast, hmid]
    have := Nat.choose_le_middle t (2 * m)
    have h2 : 2 * m / 2 = m := by omega
    rw [h2] at this
    exact_mod_cast this
noncomputable def P1 (m : ℕ) (k : ℤ) : ℝ := binomZ (2 * m) ((m : ℤ) + k) / 4 ^ m
lemma P1_zero_step (k : ℤ) : P1 0 k = if k = 0 then 1 else 0 := by
  have h : P1 0 k = binomZ 0 k := by
    unfold P1; norm_num
  rw [h]
  unfold binomZ
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · subst hk; norm_num
  · rw [ite_eq_left (by omega), ite_eq_right (by omega),
      Nat.choose_eq_zero_of_lt (by omega : 0 < k.toNat)]
    norm_num
/-- The lazy one-step recursion, which is what makes `P1` the law of the lazy
walk: `p_{m+1}(k) = p_m(k)/2 + p_m(k-1)/4 + p_m(k+1)/4`. -/
lemma P1_succ (m : ℕ) (k : ℤ) :
    P1 (m + 1) k = P1 m k / 2 + P1 m (k - 1) / 4 + P1 m (k + 1) / 4 := by
  have hpow : (4 : ℝ) ^ (m + 1) = 4 ^ m * 4 := by ring
  have e : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  have key : binomZ (2 * (m + 1)) (((m : ℤ) + 1) + k)
      = 2 * binomZ (2 * m) ((m : ℤ) + k) + binomZ (2 * m) ((m : ℤ) + (k - 1))
        + binomZ (2 * m) ((m : ℤ) + (k + 1)) := by
    rw [e, binomZ_succ, binomZ_succ, binomZ_succ]
    have a1 : ((m : ℤ) + 1 + k) - 1 - 1 = (m : ℤ) + (k - 1) := by ring
    have a2 : ((m : ℤ) + 1 + k) - 1 = (m : ℤ) + k := by ring
    have a3 : ((m : ℤ) + 1 + k) = (m : ℤ) + (k + 1) := by ring
    rw [a1, a2, a3]; ring
  unfold P1
  push_cast
  rw [hpow, key]
  field_simp
  ring
lemma P1_le_max (m : ℕ) (k : ℤ) : P1 m k ≤ P1 m 0 := by
  unfold P1
  have h0 : (m : ℤ) + 0 = (m : ℤ) := by ring
  have h4 : (0 : ℝ) ≤ ((4 : ℝ) ^ m)⁻¹ := by positivity
  rw [h0]
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right (binomZ_le_middle m ((m : ℤ) + k)) h4
lemma P1_zero_eq (m : ℕ) : P1 m 0 = (Nat.centralBinom m : ℝ) / 4 ^ m := by
  unfold P1 Nat.centralBinom
  rw [show (m : ℤ) + 0 = ((m : ℕ) : ℤ) from by ring, binomZ_natCast]
/-- The ratio of consecutive lazy walk return probabilities is `(2m+1)/(2m+2)`. -/
lemma P1_zero_succ (m : ℕ) : P1 (m + 1) 0 = (2 * m + 1) / (2 * m + 2) * P1 m 0 := by
  have key : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
      = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
    have := Nat.succ_mul_centralBinom_succ m
    have h2 : (((m + 1) * Nat.centralBinom (m + 1) : ℕ) : ℝ)
        = ((2 * (2 * m + 1) * Nat.centralBinom m : ℕ) : ℝ) := by rw [this]
    push_cast at h2
    linarith
  rw [P1_zero_eq, P1_zero_eq]
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have hm : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have hp : (4 : ℝ) ^ (m + 1) = 4 * 4 ^ m := by ring
  have hR : (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) * ((Nat.centralBinom m : ℝ) / 4 ^ m)
      = ((2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ)) / ((2 * (m : ℝ) + 2) * 4 ^ m) :=
    div_mul_div_comm _ _ _ _
  rw [hp, hR, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 * (4 : ℝ) ^ m) * key
/-- The lazy walk return probability is at most `(m+1)^{-1/2}`. -/
lemma P1_zero_le_inv_sqrt (m : ℕ) : P1 m 0 ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
  induction m with
  | zero =>
    have h0 : P1 0 0 = 1 := by rw [P1_zero_eq]; norm_num [Nat.centralBinom]
    rw [h0]
    norm_num
  | succ m ih =>
    have hs1 : Real.sqrt ((m : ℝ) + 1) > 0 := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt (((m : ℝ) + 1) + 1) > 0 := Real.sqrt_pos.mpr (by positivity)
    have e1 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (((m : ℝ) + 1) + 1) ^ 2 = ((m : ℝ) + 1) + 1 :=
      Real.sq_sqrt (by positivity)
    have hratio : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) := by positivity
    have hstep : P1 (m + 1) 0 ≤ (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) * (1 / Real.sqrt ((m : ℝ) + 1)) := by
      rw [P1_zero_succ]
      exact mul_le_mul_of_nonneg_left ih hratio
    have hfin : (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) * (1 / Real.sqrt ((m : ℝ) + 1))
        ≤ 1 / Real.sqrt (((m : ℝ) + 1) + 1) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hs1, hs2, e1, e2, sq_nonneg (Real.sqrt ((m:ℝ)+1) - Real.sqrt (((m:ℝ)+1)+1)),
        mul_pos hs1 hs2]
    calc P1 (m + 1) 0 ≤ _ := hstep
      _ ≤ 1 / Real.sqrt (((m : ℝ) + 1) + 1) := hfin
      _ = 1 / Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf
/-! ### Total variation of the discrete gradient

Symmetry and unimodality give `∑_k |p_m(k+1) - p_m(k)| = 2 p_m(0)`. -/
end LatticeProb
end
