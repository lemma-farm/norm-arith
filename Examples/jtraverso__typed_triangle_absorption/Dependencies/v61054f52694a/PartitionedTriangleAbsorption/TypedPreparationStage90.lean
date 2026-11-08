/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedDeploymentStage90
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PaddedDeploymentStage89
/-! # Nonnegative target types of the deployed padded piece

This actual producer retains the type-vector equality through deployment.
It does not assume a terminal decomposition or a catalyst insertion trace.
Token incidence and catalyst surgery remain separate obligations.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedPreparationStage90
open Finset PairMoveSelectionStage85 TypedDivisibilityCollapse PhysicalMovesStage86
variable {t : ℕ}
end PartitionedTriangleAbsorption.TypedPreparationStage90
