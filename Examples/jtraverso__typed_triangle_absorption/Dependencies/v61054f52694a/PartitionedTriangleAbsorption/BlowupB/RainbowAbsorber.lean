/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.RainbowTarget
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.GreedyEmbed
/-! # BlowupB.RainbowAbsorber — absorbers for the rainbow type, without `ThreeStepLinks`

`R3 = {{0,1,2}}` fails `ThreeStepLinks` (`not_threeStepLinks_rainbow`), so the tree's absorbers do
not apply. Here: in every graph `G` inside the rainbow blowup in which every vertex misses at most
`d` allowed neighbours, every integrally `R3`-divisible `P ⊆ E(G)` with `|P| ≤ K` has an absorber
`A` (`rainbow_private_absorber`): `A ⊆ E(G)`, `A ∩ P = ∅`, `A` and `A ∪ P` decompose, and every
vertex of `A` is a vertex of `P` or avoids a prescribed set `Z`, provided every class has more
than `|Z| + 6K + (4K + 2)(d + 1)` vertices.

Construction: the cyclic trails of `P` (`RainbowTrails`), the odd transformer with `m = 0`
(`OddTransformer`), the windmill target (`RainbowTarget`), and the greedy embedding of all fresh
vertices (`GreedyEmbed`).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset Equiv
section
variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 3} {P : Finset (Sym2 V)}
  (hdiv : IsIntDiv p R3 P)
end
end PartitionedTriangleAbsorption.BlowupB
