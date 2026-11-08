/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.CoherentTransformer.BipartiteLinkHost
public import Mathlib.Algebra.BigOperators.Fin
/-! # Refutation of the two-root coherent transformer target

In the six-class host `BipartiteLinkHost.host (k+2)`, take the two disjoint
physical 4-cycles

  `Hx = (A,0)(P,0)(Z,0)(X,0)`,  `Hy = (A,1)(P,1)(Z,1)(X,1)`.

All hypotheses of the candidate hold with `α = 1/6`, `β = 1/3`, `|I| = 4`,
for every size `n = 6(k+2)`. The star charge at `v = (A,0)` annihilates
every F0 triangle, equals `2` on `Hx` and `0` on `Hy`. By charge invariance
NO physical transformer exists, of any size.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.CoherentTransformer.Refutation
open Finset TypedApplicationLinks BipartiteLinkHost
/-- Classes along the 4-cycle: `A, P, Z, X`. -/
def cls : Fin 4 → Fin 6 := ![0, 3, 5, 1]
variable (L : ℕ)
/-- Roots of the trail with index `m`: position `i` goes to `(cls i, m)`. -/
def rootMap (m : Fin L) : Fin 4 → Fin 6 × Fin L := fun i => (cls i, m)
end PartitionedTriangleAbsorption.CoherentTransformer.Refutation
