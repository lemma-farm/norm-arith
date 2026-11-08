/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.KeevashBridge
/-! # BlowupB.KeevashPadded — the padded interface of `L3F0.KeevashF0Spec`, for every family

`L3F0/Keevash.lean` states the F₀ interface `KeevashF0Spec` (attributed there to Keevash,
*Coloured and directed designs*, arXiv:1807.05770v2, Theorem 5.15) with padded patterns, weights on
labelled embeddings (`PaddedRegular`) and extendability over all bounded templates
(`Extendable`). This file states the same shape for an arbitrary family `F` of 3-element types
on `t` classes:

* positions `PosT t m = Fin t × Fin (m + 3)` (class of `(c, j)` is `c`), `q = t (m + 3)`;
* the pattern of a type `τ`: the first `count c τ` positions of each class;
* `PaddedRegularT`: weights `y ∈ [ω n^{2−q}, ω⁻¹ n^{2−q}]` on valid copies, loads `1 ± c`;
* `ExtendableT`: every bounded template, with required pairs restricted to **allowed** class
  pairs (for `F₀` every class pair is allowed, so nothing is lost there);
* `KeevashPaddedSpec F`, with Keevash's `h = 2^{50 q³}`, `δ = 2^{−1000 q⁵}`, `c = ω^{h^{20}}`.

This part proves the counting lemma `count_ext` (sequential extensions of a partial embedding)
and `extendableT_of_cnExt`: common-neighbourhood extendability gives template extendability.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset
variable {t : ℕ}
/-- Positions of the padded patterns. -/
abbrev PosT (t m : ℕ) := Fin t × Fin (m + 3)
/-- `q = t (m + 3)`. -/
abbrev qT (t m : ℕ) : ℕ := t * (m + 3)
section Defs
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The pattern of a type: the first `count c τ` positions of each class `c`. -/
def patPosT (m : ℕ) (τ : Multiset (Fin t)) : Finset (PosT t m) :=
  univ.filter fun x => x.2.val < τ.count x.1
/-- The physical triangle of a copy. -/
def copyTriT (m : ℕ) (τ : Multiset (Fin t)) (φ : PosT t m → V) : Finset V := (patPosT m τ).image φ
/-- Class-respecting embedding of all positions. -/
def IsEmbT (m : ℕ) (p : V → Fin t) (φ : PosT t m → V) : Prop :=
  Function.Injective φ ∧ ∀ x, p (φ x) = x.1
/-- A copy of the pattern of `τ` in `J`. -/
def ValidCopyT (m : ℕ) (p : V → Fin t) (J : Finset (Sym2 V)) (τ : Multiset (Fin t))
    (φ : PosT t m → V) : Prop :=
  IsEmbT m p φ ∧ triEdges (copyTriT m τ φ) ⊆ J
open Classical in
/-- Padded regularity for the family `F`. -/
def PaddedRegularT (m : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : Finset (Sym2 V)) (ω c : ℝ) : Prop :=
  ∃ y : Multiset (Fin t) → (PosT t m → V) → ℝ,
    (∀ τ ∈ F, ∀ φ, ValidCopyT m p J τ φ →
      ω / (Fintype.card V : ℝ) ^ (qT t m - 2) ≤ y τ φ ∧
        y τ φ ≤ 1 / (ω * (Fintype.card V : ℝ) ^ (qT t m - 2))) ∧
    ∀ e ∈ J, |(∑ τ ∈ F, ∑ φ ∈ univ.filter (fun φ => ValidCopyT m p J τ φ ∧
      e ∈ triEdges (copyTriT m τ φ)), y τ φ) - 1| ≤ c
/-- The good extensions of `φ` from the roots `S` (domain `D`, labels `κ`, required pairs `T`). -/
noncomputable def goodExt {D : Type*} [Fintype D] [DecidableEq D] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V)) (κ : D → Fin t) (T : Finset (Sym2 D))
    (S : Finset D) (φ : D → V) : Finset (D → V) := by
  classical exact univ.filter fun ψ : D → V => (∀ x ∈ S, ψ x = φ x) ∧ Function.Injective ψ ∧
    (∀ x, p (ψ x) = κ x) ∧
    ∀ x y, s(x, y) ∈ T → x ≠ y → (x ∉ S ∨ y ∉ S) → AllowedPair F (κ x) (κ y) → s(ψ x, ψ y) ∈ J
/-- Template extendability for the family `F` (required pairs only on allowed class pairs). -/
def ExtendableT (K : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : Finset (Sym2 V))
    (ω : ℝ) : Prop :=
  ∀ k ≤ K, ∀ (κ : Fin k → Fin t) (S : Finset (Fin k)) (T : Finset (Sym2 (Fin k)))
    (φ : Fin k → V), Set.InjOn φ S → (∀ x ∈ S, p (φ x) = κ x) →
    ω * (Fintype.card V : ℝ) ^ (k - S.card) ≤ ((goodExt p F J κ T S φ).card : ℝ)
end Defs
/-- Keevash's `h = 2^{50 q³}`. -/
def hKT (t m : ℕ) : ℕ := 2 ^ (50 * qT t m ^ 3)
/-- Keevash's `δ = 2^{−1000 q⁵}`. -/
noncomputable def δKT (t m : ℕ) : ℝ := (2 : ℝ) ^ (-(1000 * (qT t m : ℝ) ^ 5))
/-- **Padded interface for the family `F`** (the shape of `L3F0.KeevashF0Spec`). -/
def KeevashPaddedSpec (F : Finset (Multiset (Fin t))) : Prop :=
  ∀ m : ℕ, ∃ ω0 : ℝ, 0 < ω0 ∧ ∃ n0 : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V], n0 < Fintype.card V → ∀ ω : ℝ,
      (Fintype.card V : ℝ) ^ (-δKT t m) < ω → ω < ω0 →
      ∀ (p : V → Fin t) (J : Finset (Sym2 V)), (∀ e ∈ J, ¬ e.IsDiag) →
        (∀ u v, s(u, v) ∈ J → AllowedPair F (p u) (p v)) →
        (∀ i, (Fintype.card V : ℝ) / hKT t m ≤ ((univ.filter fun v => p v = i).card : ℝ)) →
        IsIntDiv p F J → PaddedRegularT m p F J ω (ω ^ (hKT t m ^ 20)) →
        ExtendableT (qT t m * hKT t m) p F J ω → HasDecomp p F J
section Count
variable {V : Type*} [Fintype V] [DecidableEq V]
end Count
end PartitionedTriangleAbsorption.BlowupB
