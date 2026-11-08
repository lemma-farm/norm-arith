/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Sym.Sym2
/-! # Physical support of a triangle hinge

These results concern actual unordered edges, not part labels or sampled
templates. They do not construct an absorber or prove Theorem 13.16.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PhysicalHinge
variable {V : Type*} [DecidableEq V]
def support (H : Finset (Sym2 V)) : Finset V := H.biUnion Sym2.toFinset
/-- The same physical edge-set convention used in the returned definitions. -/
def triEdges (s : Finset V) : Finset (Sym2 V) :=
  s.sym2.filter (fun e => ¬ e.IsDiag)
end PartitionedTriangleAbsorption.PhysicalHinge
