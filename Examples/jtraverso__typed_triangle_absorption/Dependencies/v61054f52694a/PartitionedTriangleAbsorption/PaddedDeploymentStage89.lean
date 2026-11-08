/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PhysicalPaddingStage89
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.MoveLedgerStage88
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedDivisibilityCollapse
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedHinge.Wedge
/-! # Actual padded deployment from integral divisibility

The coefficient bound is fixed before the graph and the bounded input piece.
The padding is selected in the graph, and the deployment is produced, not
assumed. The output is not yet an absorber: its terminal configuration still
needs token-triple surgery and a positive decomposition.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PaddedDeploymentStage89
open Finset PhysicalPaddingStage89 TypedBoundedCoefficients
  PairMoveSelectionStage85 TypedDivisibilityCollapse PhysicalMovesStage86
variable {t : ℕ}
end PartitionedTriangleAbsorption.PaddedDeploymentStage89
