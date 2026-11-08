/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SelectedTripleCutStage98
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.CleanupInductionStage100
/-! # A private absorber produced by the complete physical chain

The target partition and the terminal decomposition are outputs, not inputs.
The first bridge retains catalyst freshness, needed when they are discarded
in the backwards assembly. This is a private, residue-dependent absorber.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PrivateAbsorberStage101
open Finset ColouredHub TripleCutStage94 TypedTransformer AntiEdgeSelection
  CatalystInsertionStage89 PhysicalMovesStage86 SelectedTripleCutStage98 CleanupStage100
  PairMoveAssemblyStage85
variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}
end PartitionedTriangleAbsorption.PrivateAbsorberStage101
