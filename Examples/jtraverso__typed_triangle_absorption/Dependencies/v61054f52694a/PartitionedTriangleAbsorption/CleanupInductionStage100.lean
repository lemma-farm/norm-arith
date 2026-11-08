/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.CleanupStepStage100
/-! # Producing all catalytic closures by finite induction

The induction consumes the actual invariant-preserving physical step.
Already closed blocks are skipped; no terminal decomposition is assumed.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.CleanupStage100
open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89
  TripleCutStage94 CatalyticCleanupStage99 PhysicalMovesStage86
variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))}
  {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V}
end PartitionedTriangleAbsorption.CleanupStage100
