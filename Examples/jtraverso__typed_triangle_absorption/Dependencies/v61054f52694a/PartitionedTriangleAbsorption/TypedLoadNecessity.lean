/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedNearConsumer
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedApplicationLinks
/-! # Necessary conditions for near-unit typed loads

For any family `F`, any graph `J` and any weights `ψ` on the `F`-copies of `J`,
the edge loads satisfy exact linear identities: every linear functional on the
ordered edge-count space that annihilates all type edge vectors of `F` has zero
load-weighted sum over `E(J)`. Consequently near-unit loads force the edge
vector of `J` to lie close to the span of the type edge vectors, at the same
precision as the loads. Similarly, every vertex-cone face gives a one-sided
inequality at every vertex, using only nonnegativity of the weights.

These are necessary conditions only. No sufficiency is claimed here.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedLoadNecessity
open Finset TypedNibble
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
end PartitionedTriangleAbsorption.TypedLoadNecessity
