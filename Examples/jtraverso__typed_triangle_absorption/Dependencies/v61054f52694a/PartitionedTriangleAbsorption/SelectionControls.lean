/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.AntiEdgeSelection
/-! # Finite controls: the exclusion budget must be strict

In the complete graph on seven vertices, roots 0 and 1 have five candidates.
Four blocked root edges and one excluded vertex remove every candidate.
Freeing one blocked edge restores exactly one candidate.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.AntiEdgeSelection.Controls
def candidates : Finset (Fin 7) := {2, 3, 4, 5, 6}
end PartitionedTriangleAbsorption.AntiEdgeSelection.Controls
