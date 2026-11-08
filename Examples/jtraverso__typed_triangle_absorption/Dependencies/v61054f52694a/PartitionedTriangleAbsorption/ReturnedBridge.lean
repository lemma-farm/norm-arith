/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ReturnedBasic
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PhysicalHinge
/-! # Consume Aristotle's actual decomposition definitions

No incomplete main theorem is imported. The physical-support lemmas apply to
the supplied `HasDecomp` directly, via forgetting labels and disjointness.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption
variable {V : Type*} [DecidableEq V] {t : ℕ}
lemma triEdges_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [triEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
      Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [eq_comm]
end PartitionedTriangleAbsorption
