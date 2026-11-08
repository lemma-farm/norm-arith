/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.Cost
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedTransformerLabels
/-! # BlowupB.OddLinks — admissible transitions from integral divisibility, for every family

The tree's transformer needs, at every root class `r`, a walk of length exactly `3` in the link
of `r` between any two labels (`ThreeStepLinks`). Here only **odd** walks are used.

* `LinkWalk F r n a b`: a walk of length `n` from `a` to `b` in the link of `r`
  (`Link F r a b ↔ {r, a, b} ∈ F`); `OddR`, `EvenR`: odd / even reachability.
* `Balanced F r d`: for every class `a`, the `d`-weight of the classes at even distance from `a`
  equals the weight at odd distance, and the weight of the component of `a` is even.
* `balanced_of_lattice`: every vector of the degree lattice at `r` (Definition 13.5) is balanced.
* `exists_odd_pairing`: a nonnegative balanced vector splits into pairs `e_a + e_b` with an odd
  link walk between `a` and `b`.

Consequence (`exists_odd_pairing_of_isIntDiv`): for **every** family, at every vertex of an
integrally divisible edge set the incident edges can be paired into transitions `a → r → b`
joined by an odd walk in the link of `r`. These are exactly the transitions an odd-length
transformer can realize; for the rainbow type `{0,1,2}` they are the non-reversing transitions.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset TypedTransformer
variable {t : ℕ}
/-! ### Walks in a link -/
/-- A walk of length `n` from `a` to `b` in the link of `r`. -/
inductive LinkWalk (F : Finset (Multiset (Fin t))) (r : Fin t) : ℕ → Fin t → Fin t → Prop
  | nil (a : Fin t) : LinkWalk F r 0 a a
  | cons {n : ℕ} {a b c : Fin t} : Link F r a b → LinkWalk F r n b c → LinkWalk F r (n + 1) a c
namespace LinkWalk
variable {F : Finset (Multiset (Fin t))} {r : Fin t}
theorem single {a b : Fin t} (h : Link F r a b) : LinkWalk F r 1 a b := cons h (nil b)
theorem append {m n : ℕ} {a b c : Fin t} (h₁ : LinkWalk F r m a b) (h₂ : LinkWalk F r n b c) :
    LinkWalk F r (m + n) a c := by
  induction h₁ with
  | nil _ => simpa using h₂
  | @cons k a' b' c' hl _ ih =>
    have := cons hl (ih h₂)
    rwa [show k + n + 1 = k + 1 + n by omega] at this
theorem reverse {n : ℕ} {a b : Fin t} (h : LinkWalk F r n a b) : LinkWalk F r n b a := by
  induction h with
  | nil a => exact nil a
  | @cons k a' b' c' hl _ ih => exact ih.append (single ((link_swap F r a' b').mp hl))
end LinkWalk
/-- `a` and `b` are joined by an odd walk in the link of `r`. -/
def OddR (F : Finset (Multiset (Fin t))) (r a b : Fin t) : Prop :=
  ∃ n, LinkWalk F r (2 * n + 1) a b
/-- `a` and `b` are joined by an even walk in the link of `r`. -/
def EvenR (F : Finset (Multiset (Fin t))) (r a b : Fin t) : Prop :=
  ∃ n, LinkWalk F r (2 * n) a b
section Reach
variable {F : Finset (Multiset (Fin t))} {r : Fin t} {a b c : Fin t}
theorem OddR.symm (h : OddR F r a b) : OddR F r b a := by
  obtain ⟨n, w⟩ := h; exact ⟨n, w.reverse⟩
theorem EvenR.symm (h : EvenR F r a b) : EvenR F r b a := by
  obtain ⟨n, w⟩ := h; exact ⟨n, w.reverse⟩
end Reach
/-! ### The balance invariants -/
open Classical in
/-- Weight at even distance from `a`. -/
noncomputable def evSum (F : Finset (Multiset (Fin t))) (r a : Fin t) (d : Fin t → ℤ) : ℤ :=
  ∑ b ∈ univ.filter (EvenR F r a), d b
open Classical in
/-- Weight at odd distance from `a`. -/
noncomputable def odSum (F : Finset (Multiset (Fin t))) (r a : Fin t) (d : Fin t → ℤ) : ℤ :=
  ∑ b ∈ univ.filter (OddR F r a), d b
open Classical in
/-- Weight of the link component of `a`. -/
noncomputable def compSum (F : Finset (Multiset (Fin t))) (r a : Fin t) (d : Fin t → ℤ) : ℤ :=
  ∑ b ∈ univ.filter (fun b => EvenR F r a b ∨ OddR F r a b), d b
/-- The balance invariants of a vector at the root `r`. -/
def Balanced (F : Finset (Multiset (Fin t))) (r : Fin t) (d : Fin t → ℤ) : Prop :=
  ∀ a, evSum F r a d = odSum F r a d ∧ Even (compSum F r a d)
section Balance
variable {F : Finset (Multiset (Fin t))} {r : Fin t}
theorem Balanced.zero : Balanced F r 0 := by
  intro a
  simp [evSum, odSum, compSum]
theorem Balanced.add {d₁ d₂ : Fin t → ℤ} (h₁ : Balanced F r d₁) (h₂ : Balanced F r d₂) :
    Balanced F r (d₁ + d₂) := by
  intro a
  obtain ⟨h₁a, h₁b⟩ := h₁ a
  obtain ⟨h₂a, h₂b⟩ := h₂ a
  refine ⟨?_, ?_⟩
  · simp only [evSum, odSum, Pi.add_apply, sum_add_distrib] at *
    rw [h₁a, h₂a]
  · simp only [compSum, Pi.add_apply, sum_add_distrib] at *
    exact h₁b.add h₂b
theorem Balanced.smul {d : Fin t → ℤ} (h : Balanced F r d) (k : ℤ) : Balanced F r (k • d) := by
  intro a
  obtain ⟨ha, hb⟩ := h a
  refine ⟨?_, ?_⟩
  · simp only [evSum, odSum, Pi.smul_apply, smul_eq_mul, ← mul_sum] at *
    rw [ha]
  · simp only [compSum, Pi.smul_apply, smul_eq_mul, ← mul_sum] at *
    exact hb.mul_left k
theorem Balanced.sub {d₁ d₂ : Fin t → ℤ} (h₁ : Balanced F r d₁) (h₂ : Balanced F r d₂) :
    Balanced F r (d₁ - d₂) := by
  have := h₁.add (h₂.smul (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at this
theorem Balanced.sum {ι : Type*} (s : Finset ι) (f : ι → Fin t → ℤ)
    (h : ∀ i ∈ s, Balanced F r (f i)) : Balanced F r (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact Balanced.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
end Balance
/-! ### Pairing -/
section Pairing
variable {F : Finset (Multiset (Fin t))} {r : Fin t}
end Pairing
/-! ### The rainbow type: odd transitions are the non-reversing ones -/
end PartitionedTriangleAbsorption.BlowupB
