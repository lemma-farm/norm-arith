/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.ColouredHub.Main
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.TypedBoundedCoefficients
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.OrdinaryDecompositionTransport
/-! # Signed-lattice pieces of bounded size

Combine the coloured-hub producer with the accepted Stage35 padding results:

* `TypedBoundedCoefficients.bounded_padding_package` chooses, for fixed `F` and `K`, a bound
  `B` **before** the vertex type, the partition and the piece; for `|P| ≤ K` with an integral
  global coefficient vector it supplies decomposable fresh padding `Q` (at most `3B` edges,
  disjoint from `P`, meeting no original vertex) such that `P ∪ Q` has the nonnegative
  coefficients `max (c τ) 0`;
* padding preserves even degrees and looplessness (`padded_even`, `padded_loopless`);
* the producer gives an absorber `A'` of `P ∪ Q`; then `A' ∪ Q` absorbs `P`
  (`TypedLatticePadding.absorber_of_padding`).

Bounds: `|A| ≤ 105 (|P| + |Q|) + |Q| ≤ 105 K + 318 B`, at most `34 K + 105 B + t` new vertices,
and `d_A(v) = 4 d_P(v)` at original vertices. `B` is existential (no explicit growth rate),
and it bounds the coefficient witness *chosen* here, not an arbitrary supplied witness.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.ColouredHub
open Finset PrivateTemplate TypedTransformer AntiEdgeSelection OnePart TypedLatticePadding
  TypedPaddingProducer TypedBoundedCoefficients
variable {t : ℕ}
/-! ### Transport and degree facts -/
section Transport
variable {W V : Type*} [DecidableEq W] [DecidableEq V]
/-- Typed decompositions transport along part-preserving injective vertex maps. -/
theorem hasDecomp_image_typed {q : W → Fin t} {q' : V → Fin t} {F : Finset (Multiset (Fin t))}
    (f : W → V) (hf : Function.Injective f) (hq : ∀ w, q' (f w) = q w)
    (E : Finset (Sym2 W)) (hE : HasDecomp q F E) :
    HasDecomp q' F (E.image (Sym2.map f)) := by
  obtain ⟨D, htri, hdis, hcover⟩ := hE
  refine ⟨D.image (fun s => s.image f), ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s, hpre, rfl⟩ := mem_image.mp hs
    refine ⟨(card_image_of_injective s hf).trans (htri s hpre).1, ?_⟩
    rw [image_val_of_injOn hf.injOn, Multiset.map_map]
    have : q' ∘ f = q := funext hq
    rw [this]
    exact (htri s hpre).2
  · intro s hs s' hs' hne
    obtain ⟨s, hpre, rfl⟩ := mem_image.mp hs
    obtain ⟨s', hpre', rfl⟩ := mem_image.mp hs'
    change Disjoint (triEdges (s.image f)) (triEdges (s'.image f))
    rw [OrdinaryDecompositionTransport.triEdges_image f hf,
      OrdinaryDecompositionTransport.triEdges_image f hf, disjoint_left]
    intro e he he'
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    obtain ⟨b, hb, hab⟩ := mem_image.mp he'
    have hab' : b = a := Sym2.map.injective hf hab
    subst b
    exact disjoint_left.mp (hdis hpre hpre' (fun h => hne (h ▸ rfl))) ha hb
  · rw [image_biUnion]
    simp_rw [OrdinaryDecompositionTransport.triEdges_image f hf]
    rw [← biUnion_image, hcover]
/-- Degrees are preserved by an injective vertex map. -/
theorem incidentLoad_image_apply (f : W → V) (hf : Function.Injective f) (E : Finset (Sym2 W))
    (w : W) : incidentLoad (E.image (Sym2.map f)) (f w) = incidentLoad E w := by
  unfold incidentLoad
  rw [filter_image, card_image_of_injective _ (Sym2.map.injective hf)]
  congr 1
  ext e
  simp [Sym2.mem_map, hf.eq_iff]
omit [DecidableEq W] in
/-- Vertices outside the image have degree zero in the image. -/
theorem incidentLoad_image_of_notMem (f : W → V) (E : Finset (Sym2 W)) (v : V)
    (hv : ∀ w, f w ≠ v) : incidentLoad (E.image (Sym2.map f)) v = 0 := by
  unfold incidentLoad
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hve
  obtain ⟨e', -, rfl⟩ := mem_image.mp he
  obtain ⟨w, -, rfl⟩ := Sym2.mem_map.mp hve
  exact hv w rfl
omit [DecidableEq V] in
/-- A decomposable edge set has even degrees. -/
theorem even_incidentLoad_of_hasDecomp {q : W → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 W)} (hE : HasDecomp q F E) (v : W) : Even (incidentLoad E v) := by
  obtain ⟨D, htri, hdis, rfl⟩ := hE
  refine even_incidentLoad_biUnion D triEdges hdis (fun s hs u => ?_) v
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp (htri s hs).1
  rw [triEdges_three hab hac hbc]
  have e : ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 W)) = {s(a, b), s(b, c), s(c, a)} := by
    ext x; simp only [mem_insert, mem_singleton, Sym2.eq_swap (a := a) (b := c)]; tauto
  rw [e]
  exact PrivateTemplate.even_incidentLoad_tri hab hac hbc u
omit [DecidableEq V] in
/-- A decomposable edge set is loopless. -/
theorem loopless_of_hasDecomp {q : W → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 W)} (hE : HasDecomp q F E) : ∀ e ∈ E, ¬ e.IsDiag := by
  obtain ⟨D, -, -, rfl⟩ := hE
  intro e he
  obtain ⟨s, -, hs⟩ := mem_biUnion.mp he
  exact (mem_filter.mp hs).2
end Transport
/-! ### Padding preserves the hypotheses of the producer -/
section Padding
variable {W T : Type*} [DecidableEq W] [Fintype T] [DecidableEq T]
/-- **Padding preserves even degrees.** -/
theorem padded_even {q : Ext W T → Fin t} {F : Finset (Multiset (Fin t))}
    (P : Finset (Sym2 W)) (heven : ∀ v, Even (incidentLoad P v))
    (hQ : HasDecomp q F (padding (W := W) (T := T))) (v : Ext W T) :
    Even (incidentLoad (liftE (T := T) P ∪ padding (W := W) (T := T)) v) := by
  refine even_incidentLoad_union (padding_disjoint_lift P) (fun u => ?_)
    (even_incidentLoad_of_hasDecomp hQ) v
  rcases u with w | x
  · rw [liftE, incidentLoad_image_apply Sum.inl Sum.inl_injective]; exact heven w
  · rw [liftE, incidentLoad_image_of_notMem Sum.inl P _ (fun _ => Sum.inl_ne_inr)]
    exact ⟨0, rfl⟩
/-- **Padding preserves looplessness.** -/
theorem padded_loopless {q : Ext W T → Fin t} {F : Finset (Multiset (Fin t))}
    (P : Finset (Sym2 W)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (hQ : HasDecomp q F (padding (W := W) (T := T))) :
    ∀ e ∈ liftE (T := T) P ∪ padding (W := W) (T := T), ¬ e.IsDiag := by
  intro e he
  rcases mem_union.mp he with he | he
  · obtain ⟨e', he', rfl⟩ := mem_image.mp he
    rw [Sym2.isDiag_map Sum.inl_injective]
    exact hloop e' he'
  · exact loopless_of_hasDecomp hQ e he
end Padding
/-! ### The bounded signed-lattice corollary -/
end PartitionedTriangleAbsorption.ColouredHub
