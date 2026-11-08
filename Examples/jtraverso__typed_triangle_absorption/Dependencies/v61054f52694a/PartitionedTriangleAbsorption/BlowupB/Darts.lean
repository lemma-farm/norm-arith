/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PhasedAbsorber
/-! # BlowupB.Darts — phased trail systems from vertex pairings, for every family

A **pairing** of a loopless edge set `P` is, at every vertex `v`, an involution `π v` without
fixed points of the neighbours of `v` in `P`. Following paired edges defines a permutation of the
darts of `P` (`dartNext`); reversing darts conjugates it to its inverse (`rev_zpow`), and no cycle
contains a dart together with its reverse (`not_sameCycle_rev`). Choosing, for every pair of
reverse cycles, the one containing the smaller dart (`Chosen`) gives a trail system using every
edge of `P` exactly once.

`phasedTrail_of_pairing`: if a phase `κD u v` and a centre class `ζ u v` of the darts advance by
`1`, resp. stay constant, along paired edges, darts of phase `0` start in the centre class, and
every two consecutive darts span a type of `F`, then `P` has a phased trail system — hence an
absorber (`phased_private_absorber`). No orientation of `P` has to be given in advance.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset Equiv
universe u
section Darts
variable {V : Type u} [Fintype V] [DecidableEq V] {P : Finset (Sym2 V)}
/-- Darts of `P`. -/
abbrev PDart (P : Finset (Sym2 V)) : Type u := {d : V × V // s(d.1, d.2) ∈ P}
/-- A pairing of the edges at every vertex. -/
structure Pairing (P : Finset (Sym2 V)) (π : V → V → V) : Prop where
  mem : ∀ v w, s(v, w) ∈ P → s(v, π v w) ∈ P
  invol : ∀ v w, s(v, w) ∈ P → π v (π v w) = w
  ne : ∀ v w, s(v, w) ∈ P → π v w ≠ w
variable {π : V → V → V}
theorem mem_swap' {u v : V} (h : s(u, v) ∈ P) : s(v, u) ∈ P := by rw [Sym2.eq_swap]; exact h
/-- Successor of a dart: continue along the paired edge. -/
def dartNext (hπ : Pairing P π) : Perm (PDart P) where
  toFun d := ⟨(d.1.2, π d.1.2 d.1.1), hπ.mem _ _ (mem_swap' d.2)⟩
  invFun d := ⟨(π d.1.1 d.1.2, d.1.1), mem_swap' (hπ.mem _ _ d.2)⟩
  left_inv d := by
    obtain ⟨⟨u, v⟩, h⟩ := d
    apply Subtype.ext
    simp only [Prod.mk.injEq, and_true]
    exact hπ.invol _ _ (mem_swap' h)
  right_inv d := by
    obtain ⟨⟨u, v⟩, h⟩ := d
    apply Subtype.ext
    simp only [Prod.mk.injEq, true_and]
    exact hπ.invol _ _ h
/-- Reversal of darts. -/
def dartRev (P : Finset (Sym2 V)) : Perm (PDart P) where
  toFun d := ⟨(d.1.2, d.1.1), mem_swap' d.2⟩
  invFun d := ⟨(d.1.2, d.1.1), mem_swap' d.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable (hπ : Pairing P π)
noncomputable def dartRank (d : PDart P) : ℕ := (Fintype.equivFin (PDart P) d : ℕ)
def Chosen (d : PDart P) : Prop :=
  ∃ d', (dartNext hπ).SameCycle d d' ∧ ∀ d'', ((dartNext hπ).SameCycle d d'' ∨
    (dartNext hπ).SameCycle (dartRev P d) d'') → dartRank d' ≤ dartRank d''
end Darts
end PartitionedTriangleAbsorption.BlowupB
