/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.Cost
/-! # BlowupB.Local — deletions: the reduction under a local hypothesis, with costs

`LocalHyp p F G R W` replaces "complete blowup":
* every edge of `G` is an allowed pair (`G` is contained in the complete blowup);
* every representative is adjacent in `G` to every *good* vertex (a vertex of `W`, or a
  representative) with which it forms an allowed pair.

Edges of `G` between two non-representatives may be missing arbitrarily: this covers every
graph obtained from a complete blowup by deleting edges that avoid the representatives (relative
to `W`). All gadgets of `ZeroDeg`/`Uniform` only use edges at representatives or edges of the
support, so the reduction goes through, now with explicit costs:

* `physCostZ_c4_local` (cost `4`), `physCostZ_piece_local` (cost `8`);
* `physCostZ_of_zeroDeg_local`: a balanced residual `u` costs at most `8 · l1 u`;
* `exists_deg_gadget_local` (cost `2`), `exists_copy_of_type_local`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
/-- **Local blowup hypothesis** (deletions away from the representatives). -/
structure LocalHyp (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) {q : ℕ}
    (R : Reps p q) (W : V → Prop) : Prop where
  allowed : ∀ u v, G.Adj u v → AllowedPair F (p u) (p v)
  univ : ∀ v r, (W v ∨ v ∈ R.set) → r ∈ R.set → v ≠ r → AllowedPair F (p v) (p r) → G.Adj v r
/-- Good vertices: those of `W` and the representatives. -/
def Good {p : V → Fin t} {q : ℕ} (R : Reps p q) (W : V → Prop) (v : V) : Prop := W v ∨ v ∈ R.set
/-- Every edge in the support of `w` has good endpoints. -/
def OnGood {p : V → Fin t} {q : ℕ} (R : Reps p q) (W : V → Prop) (w : Sym2 V → ℤ) : Prop :=
  ∀ e, w e ≠ 0 → ∀ x ∈ e, Good R W x
section Basic
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} {W : V → Prop}
omit [Fintype V] in
theorem LocalHyp.adj {q : ℕ} {R : Reps p q} (hL : LocalHyp p F G R W) {v r : V}
    (hv : Good R W v) (hr : r ∈ R.set) (hne : v ≠ r) (hA : AllowedPair F (p v) (p r)) :
    G.Adj v r :=
  hL.univ v r hv hr hne hA
variable {q : ℕ} {R : Reps p q}
omit [Fintype V] in
theorem OnGood.zero : OnGood R W (0 : Sym2 V → ℤ) := fun _ h => absurd rfl h
omit [Fintype V] in
theorem OnGood.add {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnGood R W w₁) (h₂ : OnGood R W w₂) :
    OnGood R W (w₁ + w₂) := by
  intro e he
  by_cases h : w₁ e = 0
  · exact h₂ e (by simpa [h] using he)
  · exact h₁ e h
omit [Fintype V] in
theorem OnGood.neg {w : Sym2 V → ℤ} (h : OnGood R W w) : OnGood R W (-w) :=
  fun e he => h e (by simpa using he)
omit [Fintype V] in
theorem OnGood.sub {w₁ w₂ : Sym2 V → ℤ} (h₁ : OnGood R W w₁) (h₂ : OnGood R W w₂) :
    OnGood R W (w₁ - w₂) := by
  rw [sub_eq_add_neg]; exact h₁.add h₂.neg
omit [Fintype V] in
theorem OnGood.smul {w : Sym2 V → ℤ} (h : OnGood R W w) (a : ℤ) : OnGood R W (a • w) :=
  fun e he => h e (by intro h0; apply he; simp [h0])
omit [Fintype V] in
theorem OnGood.sum {ι : Type*} (s : Finset ι) (f : ι → Sym2 V → ℤ)
    (h : ∀ i ∈ s, OnGood R W (f i)) : OnGood R W (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty]; exact OnGood.zero
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
end Basic
/-! ### Alternating 4-cycles, locally, with cost -/
section Pieces
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} {W : V → Prop}
end Pieces
end PartitionedTriangleAbsorption.BlowupB
