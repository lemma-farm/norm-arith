/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Sym.Sym2
/-! A finite six-vertex hinge template. This is not an abundance theorem,
an omniabsorber, or a proof of Theorem 13.16. -/
@[expose] public section
namespace PartitionedTriangleAbsorption.HingeTemplate
abbrev Vertex := Fin 6
abbrev Edge := Sym2 Vertex
def triangle (a b c : Vertex) : Finset Edge := {s(a, b), s(a, c), s(b, c)}
def leftTriangle : Finset Edge := triangle 0 2 4
def rightTriangle : Finset Edge := triangle 0 2 5
def hinge : Finset Edge :=
  {s(0, 3), s(0, 5), s(1, 2), s(1, 3), s(1, 4), s(1, 5), s(2, 5),
   s(3, 4), s(3, 5)} \ (leftTriangle ∪ rightTriangle)
end PartitionedTriangleAbsorption.HingeTemplate
