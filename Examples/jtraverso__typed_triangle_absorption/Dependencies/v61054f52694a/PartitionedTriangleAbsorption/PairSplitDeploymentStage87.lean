/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PairMoveSelectionStage85
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PhysicalMovesStage86
/-! # Deployment induction: splitting high-degree vertices by fresh pair moves

For an even finite physical configuration `X`, a vertex `x` of degree at least
four is split by one fresh pair move: two edges `xa, xb` of `X` are replaced
by `za, zb`, where `z` is a new vertex of label `p x` selected from the
compatible supply, and the seven-edge gadget is selected by
`PairMoveSelectionStage85.exists_physical_gadget`. The potential
`∑ v, (deg v / 2 - 1)` (natural subtraction, i.e. `max (deg v / 2 - 1) 0`)
drops by exactly one. Iterating gives an actual supported trace of at most
`|X|` moves ending in a configuration whose every vertex has degree `0` or `2`.
The quantitative choice budget `|Z| + 37 |X| + 4 (d + |U|) < a` is explicit.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PairSplitDeploymentStage87
open Finset AntiEdgeSelection TypedTransformer PairMoveSelectionStage85
  PhysicalHingeSupply PhysicalMovesStage86
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
/-! ### Degree bookkeeping -/
end PartitionedTriangleAbsorption.PairSplitDeploymentStage87
