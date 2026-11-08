/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.StructuralF3General.RefinerF0.ChargeF0
/-! # Pieces made of a lifted edge set and a set of charge tokens

The charge layer works on the vertex type `W0 ⊕ (Tok κ × Fin 8)`: the old vertices `W0`
and eight fresh vertices for every token identity. A token is a copy of `gadget sign` on its
eight vertices. A piece is `liftE A ∪ tokU S` for an edge set `A` on `W0` and a finite set
`S` of token identities. Disjointness, unions, loads, evenness and charge of such pieces are
computed componentwise.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
open Finset AntiEdgeSelection TypedRefinerCharge
/-- Token identities: private plus tokens `pp i k` of negative pieces, variable minus slots
`vm j`, buffer plus tokens `bp x` and fixed buffer minus tokens `bm y`. -/
inductive Tok (κ : Type*) where
  | pp (i : κ) (k : ℕ)
  | vm (j : ℕ)
  | bp (x : ℕ)
  | bm (y : ℕ)
  deriving DecidableEq
/-- `true` for plus tokens. -/
def Tok.sign {κ : Type*} : Tok κ → Bool
  | Tok.pp _ _ => true
  | Tok.vm _ => false
  | Tok.bp _ => true
  | Tok.bm _ => false
/-- The extended vertex type. -/
abbrev W1 (W0 κ : Type*) := W0 ⊕ (Tok κ × Fin 8)
variable {W0 : Type*} [DecidableEq W0] {κ : Type*} [DecidableEq κ]
def liftE (E : Finset (Sym2 W0)) : Finset (Sym2 (W1 W0 κ)) := mapE Sum.inl E
/-- The edges of one token. -/
def tokE (t : Tok κ) : Finset (Sym2 (W1 W0 κ)) :=
  mapE (fun j => (Sum.inr (t, j) : W1 W0 κ)) (gadget t.sign)
/-- The edges of a set of tokens. -/
def tokU (S : Finset (Tok κ)) : Finset (Sym2 (W1 W0 κ)) := S.biUnion tokE
/-- A piece: lifted old edges and tokens. -/
def piece (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) : Finset (Sym2 (W1 W0 κ)) :=
  liftE A ∪ tokU S
omit [DecidableEq W0] [DecidableEq κ] in
theorem tokEmb_inj (t : Tok κ) : Function.Injective (fun j => (Sum.inr (t, j) : W1 W0 κ)) := by
  intro a b h; simpa using h
theorem card_piece_le (A : Finset (Sym2 W0)) (S : Finset (Tok κ)) :
    (piece A S).card ≤ A.card + 8 * S.card := by
  unfold piece
  refine (card_union_le _ _).trans ?_
  rw [liftE, card_mapE Sum.inl_injective]
  refine Nat.add_le_add_left ?_ _
  unfold tokU
  refine card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun t _ => ?_
  rw [tokE, card_mapE (tokEmb_inj t)]
  exact gadget_card_le _
end PartitionedTriangleAbsorption.StructuralF3General.RefinerF0
