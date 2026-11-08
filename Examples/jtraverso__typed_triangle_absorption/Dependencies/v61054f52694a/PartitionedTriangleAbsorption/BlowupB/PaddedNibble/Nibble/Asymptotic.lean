/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.Round
/-! # The failure bound tends to zero

With truncation level `K = ⌊n^{1/4}⌋` (computed as `Nat.sqrt (Nat.sqrt n)`) and
weight cap `β = b / n`, every term of `failBound` is at most `n² e^{-cK}` for a
constant `c > 0` depending only on `bmax, γ, θ, ε`. Since `n ≤ 16 K⁴`, the bound
is at most `2560 K⁸ e^{-cK}`, which tends to zero. All thresholds are chosen
before `n` and are uniform for `0 < b ≤ bmax`.
-/
/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/Nibble/Asymptotic.lean.
Original SHA256: 1b79d9aa2da2d36974ffb49526fa4e4206c16b618ebf6b2b7dd3e986b59df0be.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
open Filter Topology
theorem sqrt_sqrt_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ Nat.sqrt (Nat.sqrt n) ∧ (Nat.sqrt (Nat.sqrt n)) ^ 4 ≤ n ∧
      n ≤ 16 * (Nat.sqrt (Nat.sqrt n)) ^ 4 := by
  set s := Nat.sqrt n
  set k := Nat.sqrt s
  have hs1 : s ^ 2 ≤ n := Nat.sqrt_le' n
  have hs2 : n < (s + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hk1 : k ^ 2 ≤ s := Nat.sqrt_le' s
  have hk2 : s < (k + 1) ^ 2 := Nat.lt_succ_sqrt' s
  have hs0 : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hn)
  have hk0 : 1 ≤ k := Nat.le_sqrt.mpr (by simpa using hs0)
  refine ⟨hk0, ?_, ?_⟩
  · calc k ^ 4 = (k ^ 2) ^ 2 := by ring
      _ ≤ s ^ 2 := Nat.pow_le_pow_left hk1 2
      _ ≤ n := hs1
  · have h1 : s + 1 ≤ (k + 1) ^ 2 := hk2
    have h2 : (k + 1) ≤ 2 * k := by omega
    calc n ≤ (s + 1) ^ 2 := hs2.le
      _ ≤ ((k + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ ((2 * k) ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left h2 2) 2
      _ = 16 * k ^ 4 := by ring
theorem rate_lin {r X n k c : ℝ} (hc : c ≤ r) (hc0 : 0 < c) (hk : 0 ≤ k) (hnk : k ≤ n)
    (hX : r * n ≤ X) : Real.exp (-X) ≤ Real.exp (-(c * k)) := by
  apply Real.exp_le_exp.mpr
  have h1 : c * k ≤ r * k := mul_le_mul_of_nonneg_right hc hk
  have h2 : r * k ≤ r * n := mul_le_mul_of_nonneg_left hnk (hc0.le.trans hc)
  linarith
theorem rate_sq {r X k c : ℝ} (hc : c ≤ r) (hc0 : 0 < c) (hk : 1 ≤ k)
    (hX : r * k ^ 2 ≤ X) : Real.exp (-X) ≤ Real.exp (-(c * k)) := by
  apply Real.exp_le_exp.mpr
  have h1 : c * k ≤ r * k := mul_le_mul_of_nonneg_right hc (by linarith)
  have h2 : r * k ≤ r * k ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (hc0.le.trans hc)
  linarith
theorem alg2 {θ γ b bmax n : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hb : 0 < b) (hbb : b ≤ bmax)
    (hn : 1 ≤ n) :
    θ / (24576 * bmax * (γ + 1 / 64)) * n ≤ θ * n / (24576 * (b / n) * (γ + 1 / 64)) := by
  have hbm : 0 < bmax := by linarith
  have hn0 : 0 < n := by linarith
  have e : θ * n / (24576 * (b / n) * (γ + 1 / 64)) = θ * n * n / (24576 * b * (γ + 1 / 64)) := by
    field_simp
  rw [e, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 < θ * n * (24576 * (γ + 1 / 64)) := by positivity
  have h2 : b * 1 ≤ bmax * n := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 h1.le]
theorem alg4 {γ θ k n : ℝ} (hγ : 0 < γ) (hθ : 0 < θ) (hk : 1 ≤ k) (hkn : k ^ 4 ≤ n) :
    γ * θ / 4704 * k ^ 2 ≤ γ * (θ * n) / (4608 * k ^ 2 + 96 * k) := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
  have h5 : 4608 * k ^ 2 + 96 * k ≤ 4704 * k ^ 2 := by nlinarith
  have h6 : 0 < γ * θ := by positivity
  have h7 : k ^ 2 * k ^ 2 ≤ n := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h5 (mul_nonneg h6.le (sq_nonneg k)),
    mul_le_mul_of_nonneg_left h7 h6.le]
theorem alg5 {γ b bmax n : ℝ} (hγ : 0 < γ) (hb : 0 < b) (hbb : b ≤ bmax) (hn : 1 ≤ n) :
    γ / (12 * bmax) * n ≤ γ * n / (12 * (b / n)) := by
  have hbm : 0 < bmax := by linarith
  have hn0 : 0 < n := by linarith
  have e : γ * n / (12 * (b / n)) = γ * n * n / (12 * b) := by field_simp
  rw [e, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 < γ * n * 12 := by positivity
  have h2 : b * 1 ≤ bmax * n := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 h1.le]
theorem alg7 {γ k n : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hk : 1 ≤ k) (hkn : k ^ 4 ≤ n) :
    γ ^ 3 / 4 * k ^ 2 ≤ γ ^ 3 * n / (2 * k ^ 2 + 2 * k * γ) := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by positivity)]
  have h5 : 2 * k ^ 2 + 2 * k * γ ≤ 4 * k ^ 2 := by nlinarith
  have h6 : 0 < γ ^ 3 := by positivity
  have h7 : k ^ 2 * k ^ 2 ≤ n := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h5 (mul_nonneg h6.le (sq_nonneg k)),
    mul_le_mul_of_nonneg_left h7 h6.le]
theorem alg9 {ε γ b bmax n : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (hb : 0 < b) (hbb : b ≤ bmax)
    (hn : 1 ≤ n) :
    (ε / 2) ^ 2 / (2 * (10 * bmax * γ + 3 * bmax * (ε / 2))) * n ≤
      (ε / 2) ^ 2 / (2 * (10 * (b / n) * γ + 3 * (b / n) * (ε / 2))) := by
  have hbm : 0 < bmax := by linarith
  have hn0 : 0 < n := by linarith
  have e : (ε / 2) ^ 2 / (2 * (10 * (b / n) * γ + 3 * (b / n) * (ε / 2))) =
      (ε / 2) ^ 2 * n / (2 * (10 * b * γ + 3 * b * (ε / 2))) := by field_simp
  rw [e, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : 2 * (10 * b * γ + 3 * b * (ε / 2)) ≤ 2 * (10 * bmax * γ + 3 * bmax * (ε / 2)) := by
    nlinarith
  have h4 : 0 < (ε / 2) ^ 2 * n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 h4.le]
theorem failBound_le_of_terms (n k : ℕ) (β γ θ ε E : ℝ) (hn : (1 : ℝ) ≤ n)
    (t1 : Real.exp (-(γ * (θ * n) / 64)) ≤ E)
    (t2 : Real.exp (-(θ * n / (24576 * β * (γ + 1 / 64)))) ≤ E)
    (t3 : Real.exp (-(γ * (θ * n) / 128)) ≤ E)
    (t4 : Real.exp (-(γ * (θ * n) / (4608 * (k : ℝ) ^ 2 + 96 * k))) ≤ E)
    (t5 : Real.exp (-(γ * n / (12 * β))) ≤ E)
    (t6 : Real.exp (-(γ ^ 2 * n / 2)) ≤ E)
    (t7 : Real.exp (-(γ ^ 3 * n / (2 * (k : ℝ) ^ 2 + 2 * k * γ))) ≤ E)
    (t8 : Real.exp (-((k : ℝ) / 8)) ≤ E)
    (t9 : Real.exp (-((ε / 2) ^ 2 / (2 * (10 * β * γ + 3 * β * (ε / 2))))) ≤ E) :
    failBound n k β γ θ ε ≤ 10 * (n : ℝ) ^ 2 * E := by
  unfold failBound
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hE : 0 ≤ E := (Real.exp_pos _).le.trans t1
  have h8 := mul_le_mul_of_nonneg_left t8 hn0
  have hA : Real.exp (-(γ * (θ * n) / 64)) +
      Real.exp (-(θ * n / (24576 * β * (γ + 1 / 64)))) +
      Real.exp (-(γ * (θ * n) / 128)) +
      Real.exp (-(γ * (θ * n) / (4608 * (k : ℝ) ^ 2 + 96 * k))) +
      Real.exp (-(γ * n / (12 * β))) + Real.exp (-(γ ^ 2 * n / 2)) +
      Real.exp (-(γ ^ 3 * n / (2 * (k : ℝ) ^ 2 + 2 * k * γ))) +
      n * Real.exp (-((k : ℝ) / 8)) ≤ 7 * E + n * E := by linarith
  have h1 := mul_le_mul_of_nonneg_left hA hn0
  have h2 : (n : ℝ) ^ 2 * (2 * Real.exp (-((ε / 2) ^ 2 / (2 * (10 * β * γ + 3 * β * (ε / 2)))))) ≤
      n ^ 2 * (2 * E) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have h3 : (n : ℝ) * (7 * E + n * E) ≤ 8 * n ^ 2 * E := by
    have : (n : ℝ) ≤ n ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hE]
  linarith
end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
