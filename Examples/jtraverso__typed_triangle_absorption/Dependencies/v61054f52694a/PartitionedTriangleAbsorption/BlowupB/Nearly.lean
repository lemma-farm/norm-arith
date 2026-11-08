/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.Deletions
/-! # BlowupB.Nearly — nearly complete blowups

If every edge of `G` is an allowed pair and every vertex misses at most `d` of its allowed
neighbours (`missDeg ≤ d`), then for any set `S` of vertices, as soon as every class has more than
`(|S| + 5t)(d + 1)` vertices, `5` representatives per class can be chosen greedily so that the
local hypothesis `LocalHyp` holds with respect to `S` (`exists_reps_local`).

**Corollary** (`physDivCost_nearly`). For every family `F` and every `K` there is `C = C(F, K)`
such that in every such `G` (any `d`) whose classes have more than `(2K + 5t)(d + 1)` vertices,
every integrally `F`-divisible `E ⊆ E(G)` with `|E| ≤ K` has a physical certificate of cost
at most `C`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
instance instDecidableAllowedPair {t : ℕ} (F : Finset (Multiset (Fin t))) (i j : Fin t) :
    Decidable (AllowedPair F i j) := by
  unfold AllowedPair; infer_instance
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj]
end PartitionedTriangleAbsorption.BlowupB
