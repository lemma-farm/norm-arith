/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PrivateTemplate.TemplateOrder
/-!
# Private absorber templates exist for every even, three-divisible loopless piece

For a finite vertex type `V` and a loopless edge set `P` with all degrees even and
`3 ∣ |P|`, the roots are the vertices incident to `P` (`Root P`), the auxiliaries are
`AuxV |P|` (`34 |P| + 1` vertices when `P ≠ ∅`, none when `P = ∅`), and the root inclusion
is `Sum.inl`.  We construct an edge set `A` on `Root P ⊕ AuxV |P|` such that

* `A` has no edge between two roots (so it is disjoint from the lifted `P`);
* `A` and `A ∪ ι(P)` both have exact ordinary triangle decompositions
  (`HasDecomp OnePart.part1 OnePart.triFam`);
* `|A| = 105 |P|` and `deg_A (ι v) = 4 deg_P v`;
* in the explicit order `rank` (roots first, then auxiliaries in a fixed injective order),
  every auxiliary has at most four neighbours among the roots and preceding auxiliaries;
* `|Root P| + |AuxV| ≤ 36 |P| + 1`, hence `≤ 1513 < 2048` for `|P| ≤ 42`, and every degree
  in `A` is at most `16384` for `|P| ≤ 42`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PrivateTemplate
open Finset OnePart AntiEdgeSelection
variable {V : Type*} [Fintype V] [DecidableEq V]
end PartitionedTriangleAbsorption.PrivateTemplate
