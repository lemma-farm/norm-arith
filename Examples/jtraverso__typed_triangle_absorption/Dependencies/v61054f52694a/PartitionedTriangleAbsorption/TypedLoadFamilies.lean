/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedLoadNecessity
/-! # Explicit global and vertex constraints for F0--F3

Each of the four application families has a bipartition `g` of its part labels
such that every permitted type has exactly two `g`-crossing edges and one
`g`-internal edge. Hence the functional "crossing count minus twice internal
count" annihilates every type, and the functional "internal degree minus
crossing degree" is a vertex-cone face at every root. Together with
`TypedLoadNecessity` these give necessary conditions for near-unit loads that
depend only on the graph `J` and the precision.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedLoadFamilies
open TypedLoadNecessity TypedApplicationLinks
theorem edgeVec_symm {V : Type*} {t : ℕ} (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = edgeVec p E j i := by
  simp only [edgeVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    rw [add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl
end PartitionedTriangleAbsorption.TypedLoadFamilies
