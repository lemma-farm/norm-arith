/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.PairMoveStage85
/-! # Backwards assembly of private absorbers from fresh pair moves

One step consumes an absorber of the next configuration and constructs an
absorber of the current configuration. Repeated steps still require an actual
fresh move sequence; its existence is not assumed to follow from divisibility.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PairMoveAssemblyStage85
open Finset
variable {V : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}
/-- Exact two-mode certificate for a private residue, with no universality claim. -/
def Absorbs (A X : Finset (Sym2 V)) : Prop :=
  Disjoint A X ∧ HasDecomp p F A ∧ HasDecomp p F (A ∪ X)
inductive FreshMoves (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (B : Finset (Sym2 V)) :
    Finset (Sym2 V) → Finset (Sym2 V) → Finset (Sym2 V) → ℕ → Prop
  | stop (U X : Finset (Sym2 V)) : FreshMoves p F B U X X 0
  | step {U X Y Q R H : Finset (Sym2 V)} {n : ℕ}
      (history : X ⊆ U) (removed : Q ⊆ X)
      (fresh : Disjoint (H ∪ R) (B ∪ U))
      (move : IsTransformer (p := p) (F := F) H Q R)
      (sizeH : H.card ≤ 7) (sizeR : R.card ≤ 2)
      (tail : FreshMoves p F B (U ∪ H ∪ R) ((X \ Q) ∪ R) Y n) :
      FreshMoves p F B U X Y (n + 1)
end PartitionedTriangleAbsorption.PairMoveAssemblyStage85
