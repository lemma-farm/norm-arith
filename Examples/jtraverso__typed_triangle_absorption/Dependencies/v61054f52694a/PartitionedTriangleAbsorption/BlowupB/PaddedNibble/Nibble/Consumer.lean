/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.Iterate
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
/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/Nibble/Consumer.lean.
Original SHA256: 2d6dc2d5ed2a002ce21a818125804914293c2dce6139a44c740d11de73f77aa3.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
open BernoulliExposure BernoulliConcentration Finset
end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
