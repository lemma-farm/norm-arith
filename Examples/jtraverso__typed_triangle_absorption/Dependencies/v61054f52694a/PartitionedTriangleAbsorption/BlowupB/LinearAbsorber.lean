/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.LinearTrails
/-! # BlowupB.LinearAbsorber — absorbers for linear families, without `ThreeStepLinks`

`linear_private_absorber`: for a linear family `F` with an orientation, in every graph `G` inside
the `F`-blowup in which every vertex misses at most `d` allowed neighbours and every class has
more than `|Z| + 6K + (4K + 2)(d + 1)` vertices, every integrally `F`-divisible `P ⊆ E(G)` with
`|P| ≤ K` has an absorber `A ⊆ E(G)`, disjoint from `P`, with `A` and `A ∪ P` decomposable, on at
most `4K` fresh vertices outside `Z ∪ V(P)`, each edge of `A` meeting them.

The construction is that of the rainbow type, run along the cycle of the type of each trail
(`LinearTrails`), with the windmill decomposed type by type (`windmill_hasDecomp_gen`).
`linear_terminal_absorber` stacks the private absorbers of all divisible subsets of a bounded
`X`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset Equiv
/-! ### The windmill for an arbitrary family -/
section WindGen
variable {I : Type*} [Fintype I] [DecidableEq I] {σ : Perm I} {W : Type*} [DecidableEq W]
  {g : Slot3 σ → W} {κ : I → Fin 3} {t : ℕ}
end WindGen
/-! ### Assembly -/
section
variable {t : ℕ} {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} (O : Orientation F) {P : Finset (Sym2 V)}
  (hL : IsLinearFam F) (hdiv : IsIntDiv p F P)
end
end PartitionedTriangleAbsorption.BlowupB
