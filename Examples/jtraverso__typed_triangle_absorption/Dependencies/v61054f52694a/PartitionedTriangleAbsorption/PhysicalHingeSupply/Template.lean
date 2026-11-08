/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.SignedHinge.Gadget
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
/-! # The seven-edge, six-vertex physical hinge template and its transport

Template vertices (`Fin 6`): `0 = u, 1 = v, 2 = w, 3 = z, 4 = x, 5 = y`.
Root copies `S = {u,v,w}`, `S' = {u,v,z}` share exactly the edge `uv`.
The hinge is `H = {uy, vx, xw, yw, xz, yz, xy}` with exact modes

* `uyw, vxw, xyz` decomposing `H ∪ {uw, vw}`;
* `uyz, vxz, xyw` decomposing `H ∪ {uz, vz}`.

Typing (`templateHinge`): if the label of `x` equals that of `u` and the label of `y`
equals that of `v`, every mode triangle has the label multiset of one root copy, so the
template is an `F`-hinge for **every** type family `F` containing the two root types
(in particular for `F0`, and whether or not the two root types differ).

Transport (`isHinge_map`): hinges, decompositions and edge sets move along any vertex
embedding `Fin 6 ↪ V`; `hingeEdges_isHinge` is the resulting statement for six distinct
physical vertices, phrased with the explicit physical edge set `hingeEdges`.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.PhysicalHingeSupply
open Finset SignedHinge
/-! ### The finite template -/
section Typing
variable {t : ℕ} {F : Finset (Multiset (Fin t))}
/-- Label multiset of a three-element template triangle. -/
theorem tri_val_map (ℓ : Fin 6 → Fin t) {a b c : Fin 6}
    (h : ({a, b, c} : Finset (Fin 6)).val = a ::ₘ b ::ₘ {c}) :
    ({a, b, c} : Finset (Fin 6)).val.map ℓ = ℓ a ::ₘ ℓ b ::ₘ {ℓ c} := by
  rw [h]; simp
end Typing
/-! ### Transport along a vertex embedding (generic in the type family) -/
section Transport
variable {W V : Type*} [DecidableEq W] [DecidableEq V] {t : ℕ} {F : Finset (Multiset (Fin t))}
/-- Edge embedding induced by a vertex embedding. -/
def edgeEmb (f : W ↪ V) : Sym2 W ↪ Sym2 V := ⟨Sym2.map f, Sym2.map.injective f.injective⟩
/-- Vertex-set embedding induced by a vertex embedding. -/
def setEmb (f : W ↪ V) : Finset W ↪ Finset V := ⟨fun s => s.map f, map_injective f⟩
theorem triEdges_map (f : W ↪ V) (s : Finset W) :
    triEdges (s.map f) = (triEdges s).map (edgeEmb f) := by
  simp only [map_eq_image, triEdges, sym2_image, filter_image, Sym2.isDiag_map f.injective]
  rfl
theorem isDecomp_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} {D : Finset (Finset W)}
    (h : IsDecomp pW F E D) : IsDecomp pV F (E.map (edgeEmb f)) (D.map (setEmb f)) := by
  obtain ⟨hT, hP, hU⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := mem_map.mp hs
    refine ⟨by simpa [setEmb] using (hT s' hs').1, ?_⟩
    simp only [setEmb, Function.Embedding.coeFn_mk, map_val, Multiset.map_map]
    have : pV ∘ f = pW := funext hp
    rw [this]; exact (hT s' hs').2
  · intro s hs u hu hsu
    simp only [coe_map, Set.mem_image, mem_coe] at hs hu
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨u', hu', rfl⟩ := hu
    have hne : s' ≠ u' := fun h => hsu (by rw [h])
    simp only [Function.onFun, setEmb, Function.Embedding.coeFn_mk, triEdges_map]
    exact (disjoint_map _).mpr (hP hs' hu' hne)
  · rw [← hU]
    ext e
    simp only [mem_biUnion, mem_map, setEmb, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨s, ⟨s', hs', rfl⟩, he⟩
      rw [triEdges_map] at he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      exact ⟨e', ⟨s', hs', he'⟩, rfl⟩
    · rintro ⟨e', ⟨s', hs', he'⟩, rfl⟩
      refine ⟨s'.map f, ⟨s', hs', rfl⟩, ?_⟩
      rw [triEdges_map]
      exact mem_map_of_mem _ he'
theorem hasDecomp_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} (h : HasDecomp pW F E) :
    HasDecomp pV F (E.map (edgeEmb f)) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨_, isDecomp_map f hp hD⟩
end Transport
/-! ### The physical hinge on six distinct vertices -/
section Physical
variable {V : Type*} [DecidableEq V] {t : ℕ} {F : Finset (Multiset (Fin t))}
def SixDistinct (u v w z x y : V) : Prop :=
  u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ u ≠ x ∧ u ≠ y ∧ v ≠ w ∧ v ≠ z ∧ v ≠ x ∧ v ≠ y ∧
    w ≠ z ∧ w ≠ x ∧ w ≠ y ∧ z ≠ x ∧ z ≠ y ∧ x ≠ y
/-- The labelling map `Fin 6 → V`, `(0,…,5) ↦ (u,v,w,z,x,y)`. -/
def sixMap (u v w z x y : V) : Fin 6 → V := ![u, v, w, z, x, y]
omit [DecidableEq V] in
theorem sixMap_injective {u v w z x y : V} (h : SixDistinct u v w z x y) :
    Function.Injective (sixMap u v w z x y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sixMap, eq_comm]
/-- The vertex embedding of the template. -/
def sixEmb {u v w z x y : V} (h : SixDistinct u v w z x y) : Fin 6 ↪ V :=
  ⟨sixMap u v w z x y, sixMap_injective h⟩
end Physical
end PartitionedTriangleAbsorption.PhysicalHingeSupply
