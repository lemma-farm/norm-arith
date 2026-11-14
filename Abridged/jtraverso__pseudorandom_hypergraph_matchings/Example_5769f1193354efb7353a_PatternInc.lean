module

public import Mathlib

-- ==== Examples.jtraverso__pseudorandom_hypergraph_matchings.Dependencies.vb14578f5b170.PseudorandomLib.Freedman ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
set_option relaxedAutoImplicit false
/-! # Freedman's inequality for stopped exposure martingales

We work in the finite product space `Fin n → α` with independent coordinates (distribution
`P i` at coordinate `i`), revealed in the order `0, 1, …, n - 1`.

A process is a sequence `X k : (Fin n → α) → ℝ` where `X k` only depends on the coordinates
`< k` (`Adapted`). It is a martingale if `X i ω = ∑ₐ P i a · X (i+1) (ω[i ↦ a])`.

`freedman_upper`: if, as long as the "good" events `G 0, …, G i` hold, the increments are
bounded by `C` and the accumulated conditional expected absolute increments are at most `s`,
then `P[X n - X 0 ≥ λ and all G i hold] ≤ exp(-λ² / (2C(λ + s)))`. This is Freedman's
inequality applied to the process stopped at the first bad time.
-/
@[expose] public section
namespace Pseudorandom
open Finset
section Resample
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}
end Resample
section Freedman
variable {α : Type*} [Fintype α] {n : ℕ}

noncomputable def condAbsInc (P : Fin n → α → ℝ) (X : ℕ → (Fin n → α) → ℝ) (i : Fin n)
    (ω : Fin n → α) : ℝ :=
  ∑ a, P i a * |X (i + 1) (Function.update ω i a) - X i ω|
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
end Freedman
end Pseudorandom

end
end

-- ==== Examples.jtraverso__pseudorandom_hypergraph_matchings.Dependencies.vb14578f5b170.PseudorandomLib.Cylinder ====
public section
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
set_option relaxedAutoImplicit false
/-! # Concentration of weighted counts of monochromatic sets

Colour every coordinate `v ∈ ι` independently and uniformly with one of `m` colours. For a
family of sets `B s ⊆ ι` with weights `w s ≥ 0`, consider the weighted number of sets that are
entirely coloured with the fixed colour `a`:

  `cyl S w B a ω = ∑_{s ∈ S} w s · [ω ≡ a on B s]`.

Its expectation is `∑ w s m^{-|B s|}`, and it is concentrated by the Bernstein-type
bounded-differences inequality of `Bernstein.lean`: coordinate `v` changes it by at most
`c v = ∑_{s : v ∈ B s} w s`, and only if one of the two colours is `a`.
-/
@[expose] public section
namespace Pseudorandom
open Finset
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]
/-- The uniform distribution on `m` colours at every coordinate. -/
noncomputable def unif (ι : Type*) (m : ℕ) : ι → Fin m → ℝ := fun _ _ => 1 / m
end Pseudorandom

end
end

-- ==== Examples.jtraverso__pseudorandom_hypergraph_matchings.Dependencies.vb14578f5b170.PseudorandomLib.PatternCount ====
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

-- ==== Examples.jtraverso__pseudorandom_hypergraph_matchings.Examples.Example_5769f1193354efb7353a_PatternInc ====
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
