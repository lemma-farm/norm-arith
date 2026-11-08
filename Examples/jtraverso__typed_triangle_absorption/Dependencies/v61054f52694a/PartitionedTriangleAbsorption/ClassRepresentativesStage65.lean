/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.F0Geometric.CommonNeighbour
/-! # Structural representatives after bounded physical edge deletion

The old query-deletion lemma is reused with an indicator of ONE structural
class. Roots in that class are excluded explicitly; no coarse CN5/CN6 is claimed.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.ClassRepresentativesStage65
open Finset F0Geometric
variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
def classSet (cls : V → C) (i : C) : Finset V := univ.filter (fun v => cls v = i)
end PartitionedTriangleAbsorption.ClassRepresentativesStage65
