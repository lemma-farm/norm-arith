/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.LinearExtras
/-! # BlowupB.UnifiedAbsorber — the terminal absorber for every covered family

**Theorem** (`terminal_absorber_covered`). Let `F` be a family of triangle types which is
linear or satisfies `ThreeStepLinks`. For every `K`, `γ > 0`, `η > 0` there are `N` and `δ > 0`
such that: if `G` lies inside the `F`-blowup of `p` on `n ≥ N` vertices, every vertex misses at
most `d ≤ δ n` allowed neighbours, every class has at least `γ n` vertices, `B` is an edge set of
maximum degree at most `δ n` and `X ⊆ E(G) \ B` has at most `K` edges, then there is
`C ⊆ E(G) \ (B ∪ X)` of maximum degree at most `η n`, decomposable, such that `C ∪ L` decomposes
for every integrally divisible `L ⊆ X`.

The two cases use different constructions: the tree's transformer chain
(`terminal_absorber_nearly`, via `BoundedCoreStage104`) for `ThreeStepLinks`, the windmill
absorbers of `LinearAbsorber` for linear families (`not_threeStepLinks_of_linear`: the two
classes are disjoint).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset TypedTransformer
section Helpers
variable {V : Type*} [Fintype V] [DecidableEq V]
def delEdges (G : SimpleGraph V) (B : Finset (Sym2 V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ s(u, v) ∉ B
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun v h => G.irrefl h.1⟩
instance instDecRelDelEdges (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V)) :
    DecidableRel (delEdges G B).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ s(u, v) ∉ B))
end Helpers
end PartitionedTriangleAbsorption.BlowupB
