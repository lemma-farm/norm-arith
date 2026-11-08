/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.HingeCounting
/-! # Extra support constraints genuinely remove free choices

These counts apply only to excluded vertices outside the fixed roots. An
edge whose two endpoints are roots imposes no extra support constraint.
No replacement of the returned `Hingeful` definition is introduced.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51
open Finset PhysicalHinge
variable {V : Type*} [Fintype V] [DecidableEq V]
end PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51
