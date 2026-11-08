/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.K5EdgeGadget
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-! # Exact repair from a supplied finite edge kernel

The incidence matrix and its right inverse are explicit inputs. The existence
and load bound of a physical host kernel are not asserted by this consumer.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.FinitePackingRepair
open Finset
variable {E T : Type*} [Fintype E] [Fintype T]
def mass (A : E → T → ℝ) (w : T → ℝ) (e : E) : ℝ :=
  ∑ t, A e t * w t
end PartitionedTriangleAbsorption.FinitePackingRepair
