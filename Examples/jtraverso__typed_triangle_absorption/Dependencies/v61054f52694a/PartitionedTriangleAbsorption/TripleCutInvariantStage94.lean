/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TripleCutLocalStage94
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedCatalystBridgeStage93
/-! # The boundary invariant between complete triple cuts

Tokens are those of the accepted insertion return,
`S.tokens = Y.disjSum (A × univ)`: original tokens `inl e` and catalytic
tokens `inr (y, i)`. A *token state* is an arbitrary position map
`pos : Tok V → Sym2 V`; `R ⊆ Y` is the set of original tokens not yet cut.

`Bdry p F S pos R` is the invariant at complete-triple boundaries:

* every endpoint `v` of a remaining original token `e` is a *carrier*: exactly
  `e` and one catalytic token `(y, i)`, `i ≠ 2`, sit at `v`, and that token is
  `v – catV S y i` (where `catV S y 0 = cs y`, `catV S y 1 = ct y`);
* the old catalytic vertices `cs y`, `ct y` carry exactly `(y,0),(y,2)` and
  `(y,1),(y,2)`; the catalytic handle tokens are `h – cs y`, `h' – ct y`,
  `cs y – ct y` with `p h = p h' = p y`;
* every other vertex carries nothing, exactly two catalytic tokens, or exactly
  two finished original tokens;
* finished original tokens sit at vertices carrying exactly two finished
  original tokens, and the finished original edges decompose into allowed
  triangles.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.TripleCutStage94
open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89
variable {V : Type*} [DecidableEq V] {t : ℕ}
/-- Original tokens `inl e` and catalytic tokens `inr (y, i)`. -/
abbrev Tok (V : Type*) := Sym2 V ⊕ (V × Fin 3)
/-- The tokens sitting at `v` under the position map `pos`. -/
def tokAtP (S : Data V) (pos : Tok V → Sym2 V) (v : V) : Finset (Tok V) :=
  S.tokens.filter fun q => v ∈ pos q
/-- The catalytic endpoint of the catalytic token `(y, i)`, `i ≠ 2`. -/
def catV (S : Data V) (y : V) (i : Fin 3) : V := if i = 0 then S.cs y else S.ct y
/-- **The boundary invariant** after a number of complete triple cuts;
`R` is the set of original tokens still to be cut. -/
structure Bdry (p : V → Fin t) (F : Finset (Multiset (Fin t))) (S : Data V)
    (pos : Tok V → Sym2 V) (R : Finset (Sym2 V)) : Prop where
  rem : R ⊆ S.Y
  /-- A remaining original token keeps its endpoint-label type. -/
  type : ∀ e ∈ R, Sym2.map p (pos (.inl e)) = Sym2.map p e
  /-- Carriers: exactly one remaining original and one catalytic token. -/
  carrier : ∀ e ∈ R, ∀ v ∈ pos (.inl e), ∃ y ∈ S.A, ∃ i : Fin 3, i ≠ 2 ∧
    pos (.inr (y, i)) = s(v, catV S y i) ∧ tokAtP S pos v = {.inl e, .inr (y, i)}
  at_cs : ∀ y ∈ S.A, tokAtP S pos (S.cs y) = {.inr (y, 0), .inr (y, 2)}
  at_ct : ∀ y ∈ S.A, tokAtP S pos (S.ct y) = {.inr (y, 1), .inr (y, 2)}
  /-- Catalytic handles keep their catalytic endpoint, and the other endpoint
  has the label of the old active vertex. -/
  handle : ∀ y ∈ S.A, ∀ i : Fin 3, i ≠ 2 →
    ∃ h, pos (.inr (y, i)) = s(h, catV S y i) ∧ p h = p y
  handle₂ : ∀ y ∈ S.A, pos (.inr (y, 2)) = s(S.cs y, S.ct y)
  /-- Every non-carrier vertex is empty, catalytic, or a finished-triangle vertex. -/
  other : ∀ v, (∀ e ∈ R, v ∉ pos (.inl e)) →
    tokAtP S pos v = ∅ ∨
    (∃ κ κ' : V × Fin 3, κ ≠ κ' ∧ tokAtP S pos v = {.inr κ, .inr κ'}) ∨
    (∃ e e', e ∈ S.Y \ R ∧ e' ∈ S.Y \ R ∧ e ≠ e' ∧ tokAtP S pos v = {.inl e, .inl e'})
  /-- Finished original tokens are isolated from everything else. -/
  done_iso : ∀ e ∈ S.Y \ R, ∀ v ∈ pos (.inl e), ∃ e', e' ∈ S.Y \ R ∧ e' ≠ e ∧
    tokAtP S pos v = {.inl e, .inl e'}
  /-- The finished original edges decompose into allowed triangles. -/
  done_decomp : HasDecomp p F ((S.Y \ R).image fun e => pos (.inl e))
section basic
variable {S : Data V} {pos : Tok V → Sym2 V}
end basic
section derived
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {S : Data V}
  {pos : Tok V → Sym2 V} {R : Finset (Sym2 V)}
end derived
end PartitionedTriangleAbsorption.TripleCutStage94
