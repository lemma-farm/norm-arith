/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.IntegerCertificate.Combination
public import Mathlib.Algebra.BigOperators.Fin
/-! # The two numerical consequences of `IsIntDiv p F0 P`

For a loopless edge set `P` (in particular for `P ⊆ G.edgeFinset`):

* `even_degree_of_isIntDiv`: every vertex has even degree in `P` — every F0 type degree
  vector has coordinate sum `2`;
* `charge_ind_of_isIntDiv`: the F0 charge `crossing - 2·internal` of `P` vanishes — it
  vanishes on both F0 type edge vectors.

These are proved against the actual ordered-vector conventions of `IsIntDiv`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.IntegerCertificate
open Finset SignedCertificate TypedApplicationLinks
variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 2}
/-- Degree of `y` in the edge set `P`. -/
def deg (P : Finset (Sym2 V)) (y : V) : ℕ := (P.filter (y ∈ ·)).card
omit [Fintype V] in
theorem sum_degContrib (y : V) {e : Sym2 V} (he : ¬ e.IsDiag) :
    ∑ i, degContrib p y e i = if y ∈ e then 1 else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := by simpa using he
  have key : ∀ c d : V, ∑ i, (if c = y ∧ p d = i then (1 : ℤ) else 0) =
      if c = y then 1 else 0 := by
    intro c d
    by_cases h : c = y
    · simp [h]
    · simp [h]
  simp only [degContrib, Sym2.lift_mk, sum_add_distrib, key, Sym2.mem_iff]
  by_cases ha : a = y <;> by_cases hb : b = y
  · exact absurd (ha.trans hb.symm) hab
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb, Ne.symm ha, Ne.symm hb]
end PartitionedTriangleAbsorption.IntegerCertificate
