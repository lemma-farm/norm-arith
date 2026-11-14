module

public import Mathlib

-- ==== Examples.jtraverso__pseudorandom_hypergraph_matchings.Dependencies.v6ff766ce98c2.PseudorandomLib.PatternCount ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
set_option relaxedAutoImplicit false
/-! # Weighted counts of `ℓ`-sets with a prescribed colour pattern

The vertex set is `Fin n` with its natural order. Every vertex receives a colour in `Fin q`
uniformly at random (`unif (Fin n) q`). An `ℓ`-set `e = {v₁ < ⋯ < v_ℓ}` has pattern
`α : ℕ → Fin q` if `c(vᵢ) = α (i - 1)` for all `i`, i.e. `c v = α (rk e v)` where `rk e v` is
the number of elements of `e` below `v`.

`cnt ℓ w α c = ∑_{|e| = ℓ} w e · [e has pattern α]` is the random variable `ω(E_α)` of
Theorem 3.1. `Xp ℓ w α t` is its exposure martingale, where the colours of `0, …, t - 1`
have been revealed.
-/
@[expose] public section
namespace Pseudorandom
namespace Patt
open Finset
variable {n q : ℕ}
/-- The rank of `v` in `e`: the number of elements of `e` below `v`. -/
def rk (e : Finset (Fin n)) (v : Fin n) : ℕ := (e.filter (· < v)).card
/-- `e` has colour pattern `α` under the colouring `c`. -/
def Pat (α : ℕ → Fin q) (c : Fin n → Fin q) (e : Finset (Fin n)) : Prop :=
  ∀ v ∈ e, c v = α (rk e v)

open Classical in
/-- The exposure martingale of `cnt`: colours of the vertices `< t` are revealed. -/
noncomputable def Xp (ℓ : ℕ) (w : Finset (Fin n) → ℝ) (α : ℕ → Fin q) (t : ℕ)
    (c : Fin n → Fin q) : ℝ :=
  ∑ e ∈ powersetCard ℓ univ, w e * ((1 / (q : ℝ)) ^ (e.filter (fun v : Fin n => t ≤ (v : ℕ))).card *
    if ∀ v ∈ e, (v : ℕ) < t → c v = α (rk e v) then 1 else 0)

end Patt
end Pseudorandom

end
end

-- ==== Examples.jtraverso__pseudorandom_hypergraph_matchings.Examples.Example_d317a5a8dca6c68cbdac_PatternInc ====
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
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

open Classical in
axiom Xp_inc (α : ℕ → Fin q) (i : Fin n) (c : Fin n → Fin q) (a : Fin q) :
    Xp ℓ w α (i + 1) (Function.update c i a) - Xp ℓ w α i c =
      ∑ e ∈ (powersetCard ℓ univ).filter (fun e => i ∈ e),
        w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) *
          (if Pat α c (e.filter (· < i)) then 1 else 0)) *
          ((if a = α (rk e i) then 1 else 0) - 1 / q)

theorem abs_Xp_inc_le (hq : 0 < q) (hw : ∀ e, 0 ≤ w e) (α : ℕ → Fin q) (i : Fin n)
    (c : Fin n → Fin q) (a : Fin q) :
    |Xp ℓ w α (i + 1) (Function.update c i a) - Xp ℓ w α i c| ≤ incB ℓ w α i c := by
  classical
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [Xp_inc α i c a]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e _ => ?_)
  rw [abs_mul]
  have h0 : 0 ≤ w e * ((1 / (q : ℝ)) ^ (ℓ - 1 - rk e i) *
      (if Pat α c (e.filter (· < i)) then 1 else 0)) :=
    mul_nonneg (hw e) (mul_nonneg (by positivity) (by split_ifs <;> norm_num))
  rw [abs_of_nonneg h0]
  apply mul_le_of_le_one_right h0
  have : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hqR
  have : 0 < 1 / (q : ℝ) := by positivity
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

end Patt
end Pseudorandom
