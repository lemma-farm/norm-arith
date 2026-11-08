/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.RainbowTerminal
/-! # BlowupB.LinearTrails — admissible trails for linear families

A family is **linear** (`IsLinearFam`) if its types have three distinct classes and two distinct
classes lie in at most one type. Linear families never satisfy `ThreeStepLinks` (their links are
matchings), so the tree's absorbers do not apply to them.

An `Orientation` fixes a cyclic order `x → y → z → x` of every type. An arc of `P` is an edge
`u w` of `P` together with the type `τ` of its classes, oriented along `τ`
(`p w = cycNext τ (p u)`). Integral divisibility gives, at every vertex and for every type, as
many incoming as outgoing arcs (`card_headFib_eq_card_tailFib`), so a fibrewise bijection gives
a permutation `σ` of the arcs with `tail (σ i) = head i` and `type (σ i) = type i` (`linPerm`):
closed trails running around the cycle of a single type, whose edges are exactly `P`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {t : ℕ}
/-- A linear family. -/
structure IsLinearFam (F : Finset (Multiset (Fin t))) : Prop where
  card3 : ∀ τ ∈ F, Multiset.card τ = 3
  nodup : ∀ τ ∈ F, τ.Nodup
  unique : ∀ τ ∈ F, ∀ τ' ∈ F, ∀ a b : Fin t, a ≠ b → a ∈ τ → b ∈ τ → a ∈ τ' → b ∈ τ' →
    τ = τ'
/-- A cyclic order of every type. -/
structure Orientation (F : Finset (Multiset (Fin t))) where
  ord : Multiset (Fin t) → Fin t × Fin t × Fin t
  spec : ∀ τ ∈ F, ({(ord τ).1, (ord τ).2.1, (ord τ).2.2} : Multiset (Fin t)) = τ
section Cyc
/-- The cyclic successor `x → y → z → x`. -/
def cycNext (o : Fin t × Fin t × Fin t) (c : Fin t) : Fin t :=
  if c = o.1 then o.2.1 else if c = o.2.1 then o.2.2 else o.1
def Distinct3 (o : Fin t × Fin t × Fin t) : Prop := o.1 ≠ o.2.1 ∧ o.1 ≠ o.2.2 ∧ o.2.1 ≠ o.2.2
variable {o : Fin t × Fin t × Fin t} (hd : Distinct3 o)
include hd
end Cyc
/-! ### Linear families: distinctness and uniqueness -/
section Lin
variable {F : Finset (Multiset (Fin t))} (hL : IsLinearFam F) (O : Orientation F)
include hL
end Lin
/-! ### Arcs and trails -/
section Trails
variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} (O : Orientation F) (P : Finset (Sym2 V))
/-- Arcs: an edge of `P`, the type of its classes, oriented along the type. -/
abbrev ArcL : Type _ :=
  {a : V × V × F // s(a.1, a.2.1) ∈ P ∧ p a.1 ∈ (a.2.2 : Multiset (Fin t)) ∧
    p a.2.1 = cycNext (O.ord a.2.2) (p a.1)}
variable {O P}
def ArcL.tail (i : ArcL (p := p) O P) : V := i.1.1
def ArcL.head (i : ArcL (p := p) O P) : V := i.1.2.1
variable (hL : IsLinearFam F)
include hL
end Trails
end PartitionedTriangleAbsorption.BlowupB
