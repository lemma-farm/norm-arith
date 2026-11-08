/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedLoadFamilies
/-! # Sparsity and anti-edgefulness do not determine preparability

The reserve properties consumed by `typed_cover_down_absorption_near`
(containment, disjointness from the absorber, a maximum-degree bound and
anti-edgefulness) are monotone under adding a few more edges, except for the
degree bound, which grows only by the degree of the added set. The balance
functional, however, changes by a fixed amount per added internal edge.

Consequently: if `X₀` is any reserve and `X₁` is a set of more than
`2 τ M` edges on which an annihilating functional is at most `-1` (where `M`
is the absolute functional mass of `G`), then `X₀` and `X₀ ∪ X₁` cannot both be
followed by weights on the corresponding main graphs with all loads within `τ`
of one. Hence no preparation theorem can hold for every sparse anti-edgeful
reserve: a producer must also control the reserve's type balance.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedLoadReserveObstruction
open Finset TypedLoadNecessity TypedLoadFamilies
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
omit [Fintype V] in
theorem degBounded_union {X Y : Finset (Sym2 V)} {d e : ℝ} (hX : DegBounded X d)
    (hY : DegBounded Y e) : DegBounded (X ∪ Y) (d + e) := by
  intro v
  rw [Finset.filter_union]
  exact (Nat.cast_le.mpr (Finset.card_union_le _ _)).trans
    (by push_cast; linarith [hX v, hY v])
end PartitionedTriangleAbsorption.TypedLoadReserveObstruction
