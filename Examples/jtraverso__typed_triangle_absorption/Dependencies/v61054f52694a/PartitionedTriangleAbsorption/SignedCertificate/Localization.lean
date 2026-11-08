/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedCertificate.Reduction
/-! # Localization: pairwise-supply constructions collapse to the roots

A construction that only uses two-root common-neighbour supply adds new vertices one at a
time, each joined to at most two earlier vertices (roots or earlier new vertices). We call
the resulting total edge set `H` *2-degenerate over the roots `Z`*
(`IsDegenerateOver H Z r`, with `r` an injective ranking of the new vertices).

* `weight_zero_of_degenerate` (**rigidity**): in a 2-degenerate extension, every integer
  combination of triangles of `H` whose signed edge-sum vanishes on all edges meeting a new
  vertex has zero weight on every triangle meeting a new vertex.
* `rootAbsorber_of_degenerate` (**localization**): if a two-mode solution `(A, Q)` for a
  root-supported `P` (with `Q` outside `Z`) has `A ∪ P ∪ Q` 2-degenerate over `Z`, then
  some `A' ⊆ A` with all vertices in `Z` is already an absorber for `P`, decomposed by
  triangles inside `Z`.

Hence pairwise supply alone can only succeed when `P` already has an absorber inside the
root set. `SignedCertificate.DoubleHexagon` exhibits an actual signed-certificate input
for which no such root absorber exists.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.SignedCertificate
open Finset TypedApplicationLinks
variable {V : Type*} [Fintype V] [DecidableEq V]
end PartitionedTriangleAbsorption.SignedCertificate
