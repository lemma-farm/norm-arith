/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.Transformer
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ReturnedBridge
/-! # Physical compatibility of successive hinges

Two valid transformers with disjoint hinge edge sets cannot always be composed:
cross-overlap with a residual can leave 17 edges, which cannot be partitioned
into triangles. Choosing a fresh auxiliary vertex repairs this explicit case.
These are finite controls, not a counterexample to the absorption theorem.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption
variable {V : Type*} [DecidableEq V] {t : ℕ}
namespace Compatibility
abbrev Vertex := Fin 9
abbrev Edge := Sym2 Vertex
def p : Vertex → Fin 1 := fun _ => 0
def tri (a b c : Vertex) : Finset Vertex := {a, b, c}
def L : Finset Edge := {s(0, 2), s(1, 2)}
def M : Finset Edge := {s(0, 3), s(1, 3)}
def R : Finset Edge := {s(0, 7), s(1, 7)}
end Compatibility
end PartitionedTriangleAbsorption
