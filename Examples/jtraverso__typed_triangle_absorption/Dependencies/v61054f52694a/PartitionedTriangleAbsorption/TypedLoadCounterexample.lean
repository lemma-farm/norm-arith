/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedLoadFamilies
/-! # A physical counterexample to a seed-only typed boost for F0

The graph is the complete four-partite graph `K_{x,x,y,y}` with the two
`x`-classes in part `0` and the two `y`-classes in part `1`. Every triangle
uses three distinct classes, so it is an F0-copy. Constant weight `1/(2y)` is a
`2`-regular, `(1 - x/y)`-almost packing. On the other hand, for every real
weighting whose loads are all within `τ` of one, the F0 balance functional
forces `(y-x)^2 ≤ τ (x+y)^2`.

Consequently no input tolerance `ε > 0`, chosen independently of the target
precision `τ`, lets a regular seed alone produce `τ`-precise loads, even with
the weights allowed to be negative or uncapped. For `x ≤ y ≤ 2x` the example is
also `1/6`-anti-edgeful, so anti-edge abundance does not repair this; the
missing hypothesis is the global type balance at precision `τ`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TypedLoadCounterexample
open Finset TypedNibble TypedLoadNecessity TypedLoadFamilies TypedApplicationLinks
section Counting
variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
theorem pairVec_eq_sum_degContrib (p : V → Fin t) (e : Sym2 V) (i j : Fin t) :
    pairVec p e i j = ∑ v ∈ univ.filter (fun v => p v = i), degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, degContrib, Sym2.lift_mk, Finset.sum_add_distrib]
    rw [Finset.sum_filter, Finset.sum_filter]
    simp only [← ite_and]
    congr 1
    · rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    · rw [Finset.sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
/-- Ordered edge counts from degree vectors. -/
theorem edgeVec_eq_sum_degVec (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = ∑ v ∈ univ.filter (fun v => p v = i), degVec p E v j := by
  simp only [edgeVec, degVec, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => pairVec_eq_sum_degContrib p e i j
end Counting
section Example
/-- Class sizes of `K_{x,x,y,y}`. -/
def sz (x y : ℕ) : Fin 4 → ℕ := ![x, x, y, y]
/-- Vertices of `K_{x,x,y,y}`: a class and an index inside it. -/
abbrev KV (x y : ℕ) := Σ c : Fin 4, Fin (sz x y c)
/-- Classes `0,1` lie in part `0`; classes `2,3` lie in part `1`. -/
def cls : Fin 4 → Fin 2 := ![0, 0, 1, 1]
def kgraph (x y : ℕ) : SimpleGraph (KV x y) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩
instance (x y : ℕ) : DecidableRel (kgraph x y).Adj :=
  fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))
variable {x y : ℕ}
end Example
end PartitionedTriangleAbsorption.TypedLoadCounterexample
