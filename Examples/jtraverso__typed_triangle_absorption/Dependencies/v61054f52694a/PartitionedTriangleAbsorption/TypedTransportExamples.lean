/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedRefinerTransport
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedDivisibilityCollapse
/-! # Linear charge transport is forced, for each of F0--F3

For every `k` we take `k` vertex-disjoint copies of a twelve-vertex gadget. Each gadget is a
union of three four-cycles; the reserve is the union of all copies and the region `S` is
spanned by the inside cycles. No reserve edge joins the region to its complement. The whole
reserve is integrally divisible, the empty leftover is divisible, and their charges inside
the region differ by a fixed nonzero multiple of `k`.

Consequently every typed refiner of this reserve whose pieces are integrally divisible and
have at most `K` edges has at least `2k / K` library pieces crossing the region boundary,
for every remainder `R` disjoint from the reserve. In particular no refiner can route the
region's leftover through a boundary of bounded capacity, as the ordinary parity hierarchy
does. The pieces may be disconnected and `R` may use any vertices: the bound is about the
library, not about a geometric construction.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedTransportExamples
open Finset TypedApplicationLinks TypedTransformer TypedDivisibilityCollapse TypedRefinerCharge
  TypedRefinerTransport AntiEdgeSelection
variable {t : ℕ} {W : Type*} [DecidableEq W]
/-! ### Disjoint copies of a gadget -/
/-- Copy `j` of an edge set. -/
def liftEdges {k : ℕ} (j : Fin k) (E : Finset (Sym2 W)) : Finset (Sym2 (Fin k × W)) :=
  E.image (Sym2.map (Prod.mk j))
/-- All `k` copies. -/
def copies (k : ℕ) (E : Finset (Sym2 W)) : Finset (Sym2 (Fin k × W)) :=
  univ.biUnion fun j => liftEdges j E
omit [DecidableEq W] in
theorem map_injective {k : ℕ} (j : Fin k) :
    Function.Injective (Sym2.map (Prod.mk j : W → Fin k × W)) :=
  Sym2.map.injective (Prod.mk_right_injective j)
theorem F1_card : ∀ τ ∈ F1, Multiset.card τ = 3 := by unfold F1; decide
theorem F2_card : ∀ τ ∈ F2, Multiset.card τ = 3 := by unfold F2; decide
theorem F3_card : ∀ τ ∈ F3, Multiset.card τ = 3 := by unfold F3; decide
end PartitionedTriangleAbsorption.TypedTransportExamples
