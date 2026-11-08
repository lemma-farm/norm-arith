/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.CompleteBlowup
public import Mathlib.Tactic.Abel
/-! # BlowupB.Rectangle — step 1 of the reduction: edges ↦ canonical spokes + representative edges

For an edge `uv` of a complete `F`-blowup with representatives `R` (at least `5` per class), the
eight-triangle identity `edge_identity` rewrites `ind1 uv` modulo copies as

  `cs u (p v) + cs v (p u) + (edges among representatives)`,

where `cs x k = ind1 s(x, canon k x)` is the **canonical spoke** of `x` into class `k`
(`canon k x` is the representative of class `k` of index `0`, or of index `1` when `x` is that
representative). Summing over `E` (`step1`) gives the canonical form

  `indZ E ≡ ∑ x, ∑ k, degVec p E x k • cs x k + wRR`

at cost `8 |E|`, with `wRR` supported on representative–representative edges.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
/-! ### The eight-triangle identity -/
variable {p : V → Fin t} {q : ℕ}
/-- The canonical spoke of `x` into class `k`. -/
noncomputable def cs (R : Reps p q) (hq : 5 ≤ q) (x : V) (k : Fin t) : Sym2 V → ℤ :=
  ind1 s(x, R.canon (by omega) k x)
end PartitionedTriangleAbsorption.BlowupB
