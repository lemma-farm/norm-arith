/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.OnePartDivisibility
/-! # Exact physical transport of ordinary triangle decompositions

An injective vertex map preserves each triangle, edge disjointness and exact
coverage. No template or decomposition of its physical image is assumed.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.OrdinaryDecompositionTransport
open Finset OnePart
variable {W V : Type*} [DecidableEq W] [DecidableEq V]
theorem triEdges_image (f : W → V) (hf : Function.Injective f) (s : Finset W) :
    triEdges (s.image f) = (triEdges s).image (Sym2.map f) := by
  simp only [triEdges, sym2_image, filter_image, Sym2.isDiag_map hf]
end PartitionedTriangleAbsorption.OrdinaryDecompositionTransport
