/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ClassReserveStage65.Tails
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ClassAwareHingesStage64
/-! # Deterministic hinge count inside one sampled reserve

For the roots `S = {u,v,w}`, `S' = {u,v,z}` of the original class graph, put

* `xCand = fibre(u) \ {u}` with roots `{v, w, z}`;
* `yCand = fibre(v) \ {v}` with roots `{u, w, z}`.

If `x` is marked (edges `vx, wx, zx` sampled), `y` is marked (edges `uy, wy, zy` sampled)
and the connector `xy` is sampled, then all seven edges of
`hingeEdges u v w z x y = {uy, vx, xw, yw, xz, yz, xy}` lie in the sampled reserve.
Different pairs `(x, y)` give different edge sets (`hingeEdges_inj`), so the number of
six-vertex physical hinges inside the reserve is at least the number of sampled cross pairs
between the two marked sets.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.ClassReserveStage65
open Finset PhysicalHingeSupply SignedHinge BernoulliBlocks ClassAwareHingesStage64
variable {V : Type*} [Fintype V] [DecidableEq V]
end PartitionedTriangleAbsorption.ClassReserveStage65
