/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ReturnedBridge
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
/-! # Count physical hinges with fixed roots

The count is over edge sets, not only their vertex supports. Diagonal edges
are allowed in the counting upper bound, so the bound is deliberately loose.
No absorption theorem or corrected abundance assumption is introduced.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PhysicalHinge
variable {V : Type*} [DecidableEq V]
end PartitionedTriangleAbsorption.PhysicalHinge
namespace PartitionedTriangleAbsorption
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
end PartitionedTriangleAbsorption
