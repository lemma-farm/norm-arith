/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.Transformer
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ReturnedBridge
/-! # Decompositions assembled from groups of pairwise disjoint atoms

Generic in the type family `F`. If a family of pairwise edge-disjoint *atoms* is split into
groups whose unions are each decomposable, then the union of all atoms is decomposable.
Also: a typed triangle is decomposable, and an edge with both endpoints in a vertex set lies
in the triangle edge set of that set (used to rule out root-root edges).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.SignedHinge
open Finset
variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
theorem empty_hasDecomp : HasDecomp p F (∅ : Finset (Sym2 V)) := ⟨∅, by simp [IsDecomp]⟩
/-- A union of pairwise disjoint decomposable edge sets is decomposable. -/
theorem hasDecomp_biUnion {I : Type*} (s : Finset I) (E : I → Finset (Sym2 V))
    (hdec : ∀ i ∈ s, HasDecomp p F (E i))
    (hdis : (s : Set I).PairwiseDisjoint E) :
    HasDecomp p F (s.biUnion E) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (empty_hasDecomp (p := p) (F := F))
  | insert a s ha ih =>
    rw [biUnion_insert]
    refine HasDecomp.union (hdec a (mem_insert_self _ _))
      (ih (fun i hi => hdec i (mem_insert_of_mem hi))
        (hdis.subset (by simp))) ?_
    rw [disjoint_biUnion_right]
    intro i hi
    exact hdis (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
theorem hasDecomp_triEdges {s : Finset V} (h : IsTypedTri p F s) :
    HasDecomp p F (triEdges s) :=
  ⟨{s}, fun s' hs' => by rw [mem_singleton.mp hs']; exact h, by simp, by simp⟩
end PartitionedTriangleAbsorption.SignedHinge
