/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedLoadPreparation
/-! # A class-level obstruction to the balanced F0 boost

The graph is the complete four-partite graph with classes `0,1` in part `0` and
classes `2,3` in part `1`, of sizes `s 0, s 1, s 2, s 3`. Every triangle uses
three distinct classes, and all of them are F0-copies.

Besides the F0 type functional, the edge function `parZ` (`+1` on the edges
between classes `0,2` and `1,3`, `-1` between `0,3` and `1,2`, zero on internal
edges) vanishes on every triangle of this graph. Its total charge is
`2 (s 0 - s 1)(s 2 - s 3)`. This functional is not a function of the parts:
it is invisible to the global F0 balance and to the vertex-cone faces.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.F0ParallelObstruction
open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks
  TypedLoadCounterexample TypedLoadPreparation
section General
variable (s : Fin 4 → ℕ)
/-- Vertices: a class and an index inside it. -/
abbrev QV := Σ c : Fin 4, Fin (s c)
def qgraph : SimpleGraph (QV s) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩
instance : DecidableRel (qgraph s).Adj :=
  fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))
variable {s}
end General
section Family
/-- Class sizes `2k(q+12), 2k(q+6), 2k(q+8), 2kq`. They satisfy
`(a+b)(c+d) = 2(ab+cd)` exactly (zero F0 charge) while `(a-b)(c-d) = 192k^2`. -/
def fam (k q : ℕ) : Fin 4 → ℕ :=
  ![2 * k * (q + 12), 2 * k * (q + 6), 2 * k * (q + 8), 2 * k * q]
variable {k q : ℕ}
end Family
section Refutation
variable {k q : ℕ}
end Refutation
end PartitionedTriangleAbsorption.F0ParallelObstruction
