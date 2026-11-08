/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.HingeTemplate
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ReturnedBasic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
/-! # Removing an arbitrary decomposable set can cross a degree-cone boundary

Six physical vertices, two part labels, and permitted triangle types 112 and
122. This is a counterexample to an unrestricted residual-cone preservation
claim, not to Theorem 13.16. No regularity, abundance, or sparsity claim is made.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.ConeBoundary
open HingeTemplate
def part (v : Vertex) : Bool := decide (4 ≤ v.val)
end PartitionedTriangleAbsorption.ConeBoundary
