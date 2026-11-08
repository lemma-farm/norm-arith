/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SparseReserveAssembly
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.F0Geometric.CommonNeighbour
public import Mathlib.Data.Nat.Choose.Bounds
/-! # Physical reserves preserving bounded-root common-neighbour queries

This producer explicitly assumes the corresponding queries in the host.
Only the edge blocks within one query need to be disjoint; different queries
use the same probability space and are combined by a union bound.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.RootQueryReserveStage59
open Finset MeasureTheory ProbabilityTheory BernoulliBlocks
variable {V : Type*} [Fintype V] [DecidableEq V]
def Query (r : ℕ) := {R : Finset V // R.card ≤ r} × Fin 2
noncomputable instance queryFintype (r : ℕ) : Fintype (Query (V := V) r) := by
  classical
  unfold Query
  infer_instance
universe u
end PartitionedTriangleAbsorption.RootQueryReserveStage59
