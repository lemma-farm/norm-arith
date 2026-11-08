/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedApplicationLinks
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.RootedEmbeddingSelection
/-! # Root-clone supply: definitions

All sets are computed from the actual adjacency of `G` and the labels `p`;
nothing here is a geometric oracle. `n = Fintype.card V`.

* `partSet p i` is `V_i = {v : p v = i}`;
* `partNbrs p G i x` is `N_i(x) = {v : p v = i ∧ G.Adj x v}`;
* `partDeg p G i x` is `d_i(x) = |N_i(x)|`;
* `commonCount p G i x y` is `c_i(x,y) = |N_i(x) ∩ N_i(y)|`;
* `commonPart p G k x y` is the set of common neighbours of `x, y` in part `k`;
* `beta α = α² / 2`;
* `cloneSet p G α i x` is `Y_x = {y ∈ V_i : c_i(x,y) ≥ β n}`.

`Y_x` may contain `x` itself; membership in `Y_x` is not a distinctness claim.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.CloneSupply
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
def partNbrs (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin 2)
    (x : V) : Finset V :=
  univ.filter fun v => p v = i ∧ G.Adj x v
/-- `d_i(x) = |N_i(x)|`. -/
def partDeg (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj] (i : Fin 2)
    (x : V) : ℕ :=
  (partNbrs p G i x).card
omit [DecidableEq V] in
theorem mem_partNbrs {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {i : Fin 2} {x v : V} : v ∈ partNbrs p G i x ↔ p v = i ∧ G.Adj x v := by
  simp [partNbrs]
omit [DecidableEq V] in
theorem partDeg_le_card (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (x : V) : partDeg p G i x ≤ Fintype.card V :=
  card_le_univ _
theorem iji_mem_F0 (i j : Fin 2) (hij : i ≠ j) :
    ({i, j, i} : Multiset (Fin 2)) ∈ TypedApplicationLinks.F0 := by
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | decide
/-- In `Fin 2`, a label different from `i` is the other part. -/
theorem exists_other (i : Fin 2) : ∃ j : Fin 2, j ≠ i := by
  fin_cases i
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
end PartitionedTriangleAbsorption.CloneSupply
