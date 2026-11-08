/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.AbsorberHook
/-! # BlowupB.GreedyEmbed — greedy embedding of fresh vertices in nearly complete hosts

A finite set of slots `J`, each with a class `c j`, a set of fixed roots `roots j` and a
symmetric irreflexive *need* relation between slots. If every vertex misses at most `d` allowed
neighbours and every class has more than `|S| + |J| + D(d+1)` vertices, where `D` bounds the
number of roots plus needed partners of a slot, then the slots can be filled injectively with
vertices of their classes, outside `S`, adjacent to their roots and to their needed partners
(`greedy_embed`). Valid for every family.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ} {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj]
end PartitionedTriangleAbsorption.BlowupB
