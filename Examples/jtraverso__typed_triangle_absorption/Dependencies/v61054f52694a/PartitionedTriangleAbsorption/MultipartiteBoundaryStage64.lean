/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ClassAwareHingesStage64
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
/-! # A threshold host with physical hinges but no universal same-part queries

The complete graph in four equal structural classes has minimum degree 3n/4.
Grouping the classes into two parts permits abundant F0 hinges but makes a
two-root common-neighbour query in one part impossible.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.MultipartiteBoundaryStage64
open Finset TypedApplicationLinks F0Geometric SignedHinge ClassAwareHingesStage64
abbrev Vertex (s : ℕ) := Fin 4 × Fin s
def classPart (i : Fin 4) : Fin 2 := if i < 2 then 0 else 1
def part {s : ℕ} (v : Vertex s) : Fin 2 := classPart v.1
end PartitionedTriangleAbsorption.MultipartiteBoundaryStage64
