/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.Rainbow
/-! # BlowupB.ZeroDeg — balanced residuals are physical

Let `G` be a complete `F`-blowup with at least `5` vertices in every class (`Reps p 5`). An
integer edge function `u` supported on edges of `G`, with zero edge-count vector and **zero degree
vector at every vertex** (`degVecZ p u v = 0`: for every vertex and every class, the signed number
of edges into that class vanishes), is a ℤ-combination of copies (`physDivZ_of_zeroDeg`).

Proof. Fix a base vertex `o i` in each class. With
`qg uv = [uv] - [u o(p v)] - [o(p u) v] + [o(p u) o(p v)]` one has `∑ e, u e • qg e = u`: the
middle terms are the spokes weighted by the degree vectors, the last term is the edge-count
vector. Each `qg` of a cross edge is an alternating `4`-cycle (or `0`); within a class the
`qg` are regrouped against a fixed reference edge `o₁ o₂`, which is possible because the free
edges of each class have total weight `0`. Alternating `4`-cycles are physical: four copies
through a common apex `s` (`c4_identity`).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
/-! ### Closure of physical divisibility -/
section Closure
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
omit [Fintype V] in
theorem PhysDivZ.zero : PhysDivZ p F G (0 : Sym2 V → ℤ) :=
  physDivZ_of_physCostZ (PhysCostZ.zero p F G)
omit [Fintype V] in
theorem PhysDivZ.smul {w : Sym2 V → ℤ} (h : PhysDivZ p F G w) (a : ℤ) :
    PhysDivZ p F G (a • w) := by
  obtain ⟨ι, hι, T, c, hT, hw⟩ := h
  refine ⟨ι, hι, T, a • c, hT, fun e => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hw e, mul_sum]
  exact sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
omit [Fintype V] in
theorem PhysDivZ.neg {w : Sym2 V → ℤ} (h : PhysDivZ p F G w) : PhysDivZ p F G (-w) := by
  have := h.smul (-1)
  rwa [neg_one_smul] at this
omit [Fintype V] in
theorem PhysDivZ.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : PhysDivZ p F G w₁) (h₂ : PhysDivZ p F G w₂) :
    PhysDivZ p F G (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg
omit [Fintype V] in
theorem PhysDivZ.sum {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ)
    (h : ∀ i ∈ s, PhysDivZ p F G (f i)) : PhysDivZ p F G (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact PhysDivZ.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
end Closure
/-! ### Supports in `G` -/
/-- The support of `w` consists of edges of `G`. -/
def OnG (G : SimpleGraph V) (w : Sym2 V → ℤ) : Prop := ∀ e, w e ≠ 0 → e ∈ G.edgeSet
section OnGLemmas
variable {G : SimpleGraph V}
omit [Fintype V] [DecidableEq V] in
theorem OnG.add {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnG G w₁) (h₂ : OnG G w₂) : OnG G (w₁ + w₂) := by
  intro e he
  by_cases h : w₁ e = 0
  · exact h₂ e (by simpa [h] using he)
  · exact h₁ e h
omit [Fintype V] [DecidableEq V] in
theorem OnG.neg {w : Sym2 V → ℤ} (h : OnG G w) : OnG G (-w) :=
  fun e he => h e (by simpa using he)
omit [Fintype V] [DecidableEq V] in
theorem OnG.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnG G w₁) (h₂ : OnG G w₂) : OnG G (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg
end OnGLemmas
/-! ### Alternating 4-cycles are physical -/
/-- The alternating `4`-cycle `a b c d`: `[ab] - [bc] + [cd] - [da]`. -/
def c4 (a b c d : V) : Sym2 V → ℤ := ind1 s(a, b) - ind1 s(b, c) + ind1 s(c, d) - ind1 s(d, a)
variable {p : V → Fin t}
def mcls (p : V → Fin t) (i : Fin t) (e : Sym2 V) : ℤ :=
  Sym2.lift ⟨fun x y => if p x = i ∧ p y = i then 1 else 0, fun x y => by
    by_cases h1 : p x = i <;> by_cases h2 : p y = i <;> simp [h1, h2]⟩ e
/-- Coefficient of the class-`i` reference gadget: `1` on edges of class `i` avoiding the base
vertex, `0` on the other edges (and `-1` on the base loop, which carries no weight). -/
def lam (p : V → Fin t) (o : Fin t → V) (i : Fin t) (e : Sym2 V) : ℤ :=
  mcls p i e - degContrib p (o i) e i
end PartitionedTriangleAbsorption.BlowupB
