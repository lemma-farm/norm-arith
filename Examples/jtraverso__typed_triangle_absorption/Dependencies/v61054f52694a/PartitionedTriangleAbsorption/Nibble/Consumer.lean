/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.Nibble.Iterate
/-! # The ordinary nibble consumer

For fixed `b > 0` and `0 < η ≤ 1` there is `N` such that for every vertex set of
size `n ≥ N`, every family of distinct physical triangles of a graph `B`
(all three edges in `B`), with weights `0 ≤ w ≤ b/n` and exact unit load on every
edge of `B`, admits an actual edge-disjoint triangle packing `P` whose residual
graph `B \ E(P)` has maximum degree at most `η n`.

The proof runs `r` rounds of `near_load_round` (each in a fresh finite product
space on the current surviving system) with the schedule from `schedule_params`,
and maintains `IterInv`. This does NOT produce a fractional weighting on an
arbitrary dense graph and does NOT establish typed absorption.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.Nibble
open BernoulliExposure BernoulliConcentration Finset
end PartitionedTriangleAbsorption.Nibble
