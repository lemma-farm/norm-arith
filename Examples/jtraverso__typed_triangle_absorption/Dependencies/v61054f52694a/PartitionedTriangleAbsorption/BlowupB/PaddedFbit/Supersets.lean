/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedFbit.Inverse
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.PaddedTrivial.Covered
@[expose] public section
/-!
# Transfer from Fbit to its bit-only supersets

The census found five bit-only families (quotient `ℤ/2`) with the allowed pairs of Fbit:
`Fbit`, `Fbit ∪ {333}`, `Fbit ∪ {111}`, `Fbit ∪ {111, 222}`, `Fbit ∪ {111, 222, 333}`. Every extra
type is monochromatic, so it adds no allowed pair and has an even 01-count. For such an `F ⊇ Fbit`:

* the universal absorbers of Fbit are universal for `F`: an Fbit decomposition is an `F`
  decomposition, and an `F`-divisible leftover is Fbit-divisible (`F`-divisibility forces `Even3` and
  an even 01-count, i.e. `FbitGood ∧ bit = 0`, which is Fbit-divisibility);
* the Fbit ternary inverse is `F`-supported, so the copy step of the F* certificate runs for `F`.

`keevashPaddedSpec_of_fbitSuper` packages this; the four supersets are instantiated with `decide`.
-/
namespace PaddedFbit
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble
open PaddedF12
/-- The hypotheses on a superset of Fbit (all decidable for a concrete family). -/
structure FbitSuper (F : Finset (Multiset (Fin 4))) : Prop where
  sub : Fbit ⊆ F
  allowed : ∀ i j : Fin 4, (∃ k, Link F i j k) ↔ (∃ k, Link Fbit i j k)
  bit : ∀ τ ∈ F, (2 : ℤ) ∣ typeEdgeVec τ 0 1
  facts : PaddedGeneral.FamilyFacts F
theorem hasDecomp_of_subset {V : Type*} [DecidableEq V] {p : V → Fin 4}
    {F F' : Finset (Multiset (Fin 4))} (h : F ⊆ F') {E : Finset (Sym2 V)}
    (hd : HasDecomp p F E) : HasDecomp p F' E := by
  obtain ⟨D, hD, hdis, hU⟩ := hd
  exact ⟨D, fun s hs => ⟨(hD s hs).1, h (hD s hs).2⟩, hdis, hU⟩
end PaddedFbit
