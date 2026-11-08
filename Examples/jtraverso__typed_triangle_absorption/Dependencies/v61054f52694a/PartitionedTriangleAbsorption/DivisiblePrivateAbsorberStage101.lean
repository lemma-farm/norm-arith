/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PrivateAbsorberProducerStage101
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PaddedDeploymentStage89
/-! # Private absorption from bounded integral divisibility

The uniform coefficient bound is chosen before the graph and residue.
Padding, deployment, insertion, cut and cleanup are all produced in the
same physical graph. Compatible supply is still an explicit hypothesis.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PrivateAbsorberStage101
open Finset TypedTransformer TypedDivisibilityCollapse PairMoveAssemblyStage85
  AntiEdgeSelection PairMoveSelectionStage85
variable {t : ℕ}
end PartitionedTriangleAbsorption.PrivateAbsorberStage101
