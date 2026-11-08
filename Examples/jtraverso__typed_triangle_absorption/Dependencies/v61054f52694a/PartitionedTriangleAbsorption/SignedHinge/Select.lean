/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedHinge.Groups
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51
public import Mathlib.Tactic.Linarith
/-! # Explicit physical hinge supply and selection of a vertex-fresh hinge

`HingeSupply p F G β C0` is the **explicit additional hypothesis** of the Stage 53 target:
for every two actual `F`-copies `S, S'` of `G` sharing exactly one edge, some
`i ∈ [6, C0]` has at least `β n^(i-4)` distinct physical edge sets `H ⊆ E(G)` with
`IsHinge p F S S' H` and `|vertSet H| = i`. It is a new, separately named predicate; the
returned `Hingeful` (with its literal `n^(i-2)` convention) is not modified or used.

`exists_hinge_avoiding`: if `2^C(C0+1,2) |U| < β n`, a supplied hinge exists whose support
meets `U` only in its four roots. This is the **vertex-only** (`d = 0`, no blocked edges)
case of the exclusion count: it uses only the accepted Stage 51 count `one_extra_vertex`
and the four-root lemma, summed over the excluded vertices. The general union bound with
blocked edges (owned by the local team) is not needed and not reproduced.

`greedy_disjoint`: a generic greedy lemma producing pairwise vertex-disjoint fresh choices.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.SignedHinge
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
end PartitionedTriangleAbsorption.SignedHinge
