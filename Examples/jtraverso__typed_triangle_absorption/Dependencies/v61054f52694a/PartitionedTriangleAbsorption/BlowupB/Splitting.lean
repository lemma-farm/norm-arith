/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.UnifiedAbsorber
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.Family001
/-! # BlowupB.Splitting — absorbers for unions of families with disjoint pair sets

* `NearlyAbsorbing F`: the conclusion of `terminal_absorber_covered` (terminal absorbers of
  bounded sets in nearly complete `F`-blowups, avoiding a sparse forbidden set `B`).
* `nearlyAbsorbing_of_terminalShape`: terminal absorbers on few fresh vertices (the shape of
  `linear_terminal_absorber`, `phased_terminal_absorber`) give `NearlyAbsorbing`; e.g.
  `nearlyAbsorbing_001`.
* `isIntDiv_split`: if no class pair is allowed by both `F₁` and `F₂`, integral
  `F₁ ∪ F₂`-divisibility of `L` implies integral `F₁`-divisibility of the `F₁`-edges of `L`.
* **`nearlyAbsorbing_union`**: `NearlyAbsorbing` is closed under unions of families with disjoint
  allowed pairs. The absorber is the union of the absorbers of the two edge classes.

Examples: `{000, 001, 111}` (where same-class-sequence targets fail, see the census) and
`{001, 111}` (neither linear nor `ThreeStepLinks`).
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.BlowupB
open Finset TypedTransformer
variable {t : ℕ}
section Allowed
variable {V : Type*} [Fintype V] [DecidableEq V] (F : Finset (Multiset (Fin t))) (p : V → Fin t)
/-- The edge `e` joins two classes allowed by `F`. -/
def aE (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => AllowedPair F (p u) (p v),
    fun _ _ => propext ⟨AllowedPair.symm, AllowedPair.symm⟩⟩ e
variable {F p}
theorem aE_mk {u v : V} : aE F p s(u, v) ↔ AllowedPair F (p u) (p v) := Iff.rfl
theorem pairVec_cases {e : Sym2 V} {i j : Fin t} (h : pairVec p e i j ≠ 0) :
    ∃ u v, e = s(u, v) ∧ p u = i ∧ p v = j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk] at h
    by_cases h1 : p a = i ∧ p b = j
    · exact ⟨a, b, rfl, h1⟩
    · by_cases h2 : p b = i ∧ p a = j
      · exact ⟨b, a, Sym2.eq_swap, h2⟩
      · simp [h1, h2] at h
theorem degContrib_cases {v : V} {e : Sym2 V} {j : Fin t} (h : degContrib p v e j ≠ 0) :
    ∃ u, e = s(v, u) ∧ p u = j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [degContrib, Sym2.lift_mk] at h
    by_cases h1 : a = v ∧ p b = j
    · exact ⟨b, by rw [h1.1], h1.2⟩
    · by_cases h2 : b = v ∧ p a = j
      · exact ⟨a, by rw [h2.1, Sym2.eq_swap], h2.2⟩
      · simp [h1, h2] at h
end Allowed
section TypeVec
variable {τ : Multiset (Fin t)} {a i j : Fin t}
theorem pair_le_of_count {τ : Multiset (Fin t)} {i j : Fin t} (hij : i ≠ j) (hi : i ∈ τ)
    (hj : j ∈ τ) : ({i, j} : Multiset (Fin t)) ≤ τ := by
  rw [Multiset.insert_eq_cons, Multiset.le_iff_subset (Multiset.nodup_cons.mpr ⟨by simpa using hij,
    Multiset.nodup_singleton _⟩)]
  intro x hx
  simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hi
  · exact hj
theorem pair_le_of_two {τ : Multiset (Fin t)} {i : Fin t} (h : 2 ≤ τ.count i) :
    ({i, i} : Multiset (Fin t)) ≤ τ := by
  have e : ({i, i} : Multiset (Fin t)) = Multiset.replicate 2 i := by
    rw [Multiset.replicate_succ, Multiset.replicate_one]; rfl
  rw [e]
  exact Multiset.le_count_iff_replicate_le.mp h
theorem le_of_typeEdgeVec_ne (h : typeEdgeVec τ i j ≠ 0) : ({i, j} : Multiset (Fin t)) ≤ τ := by
  unfold typeEdgeVec at h
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl] at h
    apply pair_le_of_two
    have h0 : (τ.count i : ℤ) ≠ 0 := by intro h0; rw [h0] at h; simp at h
    have h1 : (τ.count i : ℤ) ≠ 1 := by intro h1; rw [h1] at h; simp at h
    omega
  · rw [if_neg hij, sub_zero] at h
    have h1 : (τ.count i : ℤ) ≠ 0 := fun h0 => h (by rw [h0, zero_mul])
    have h2 : (τ.count j : ℤ) ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
    exact pair_le_of_count hij (Multiset.count_ne_zero.mp (by exact_mod_cast h1))
      (Multiset.count_ne_zero.mp (by exact_mod_cast h2))
theorem le_of_typeDegVec_ne (ha : a ∈ τ) (h : typeDegVec τ a j ≠ 0) :
    ({a, j} : Multiset (Fin t)) ≤ τ := by
  unfold typeDegVec at h
  by_cases hja : j = a
  · subst hja
    rw [if_pos rfl] at h
    apply pair_le_of_two
    have h1 : 1 ≤ τ.count j := Multiset.one_le_count_iff_mem.mpr ha
    have h2 : (τ.count j : ℤ) ≠ 1 := fun h1' => h (by rw [h1']; norm_num)
    omega
  · rw [if_neg hja, sub_zero] at h
    exact pair_le_of_count (Ne.symm hja) ha
      (Multiset.count_ne_zero.mp (by exact_mod_cast h))
end TypeVec
/-- **Splitting divisibility.** -/
theorem isIntDiv_split {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin t}
    {F₁ F₂ : Finset (Multiset (Fin t))} (hcard : ∀ τ ∈ F₁ ∪ F₂, Multiset.card τ = 3)
    (hdisj : ∀ a b, AllowedPair F₁ a b → ¬ AllowedPair F₂ a b) {L : Finset (Sym2 V)}
    [DecidablePred (aE F₁ p)] (hdiv : IsIntDiv p (F₁ ∪ F₂) L) :
    IsIntDiv p F₁ (L.filter (aE F₁ p)) := by
  have hev : ∀ (E : Finset (Sym2 V)) i j, edgeVec p E i j = ∑ e ∈ E, pairVec p e i j := by
    intro E i j; simp only [edgeVec, Finset.sum_apply]
  have hcv : ∀ (S : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) i j,
      (∑ τ ∈ S, c τ • typeEdgeVec τ) i j = ∑ τ ∈ S, c τ * typeEdgeVec τ i j := by
    intro S c i j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hdv : ∀ (E : Finset (Sym2 V)) v j, degVec p E v j = ∑ e ∈ E, degContrib p v e j := by
    intro E v j; simp only [degVec, Finset.sum_apply]
  have hcd : ∀ (S : Finset (Multiset (Fin t))) (c : Multiset (Fin t) → ℤ) (a j : Fin t),
      (∑ τ ∈ S, c τ • typeDegVec τ a) j = ∑ τ ∈ S, c τ * typeDegVec τ a j := by
    intro S c a j; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hc1 : ∀ τ ∈ F₁, Multiset.card τ = 3 := fun τ h => hcard τ (mem_union_left _ h)
  have hc2 : ∀ τ ∈ F₂, Multiset.card τ = 3 := fun τ h => hcard τ (mem_union_right _ h)
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc⟩ := hdiv.1
    refine ⟨c, ?_⟩
    funext i j
    rw [hev, hcv]
    by_cases hA : AllowedPair F₁ i j
    · calc ∑ e ∈ L.filter (aE F₁ p), pairVec p e i j = ∑ e ∈ L, pairVec p e i j := by
            refine sum_subset (filter_subset _ _) fun e he hne => ?_
            by_contra h
            obtain ⟨u, v, rfl, hu, hv⟩ := pairVec_cases h
            exact hne (mem_filter.mpr ⟨he, by rw [aE_mk, hu, hv]; exact hA⟩)
        _ = ∑ τ ∈ F₁ ∪ F₂, c τ * typeEdgeVec τ i j := by rw [← hev, hc, hcv]
        _ = ∑ τ ∈ F₁, c τ * typeEdgeVec τ i j := by
            refine (sum_subset subset_union_left fun τ hτ hτ1 => ?_).symm
            have hτ2 : τ ∈ F₂ := (mem_union.mp hτ).resolve_left hτ1
            by_contra h
            have h' : typeEdgeVec τ i j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
            exact hdisj i j hA ⟨τ, hτ2, hc2 τ hτ2, le_of_typeEdgeVec_ne h'⟩
    · rw [sum_eq_zero, sum_eq_zero]
      · intro τ hτ
        by_contra h
        have h' : typeEdgeVec τ i j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
        exact hA ⟨τ, hτ, hc1 τ hτ, le_of_typeEdgeVec_ne h'⟩
      · intro e he
        by_contra h
        obtain ⟨u, v, rfl, hu, hv⟩ := pairVec_cases h
        have := (mem_filter.mp he).2
        rw [aE_mk, hu, hv] at this
        exact hA this
  · intro v
    obtain ⟨c, hc⟩ := hdiv.2 v
    refine ⟨c, ?_⟩
    funext j
    rw [hdv, hcd]
    by_cases hA : AllowedPair F₁ (p v) j
    · calc ∑ e ∈ L.filter (aE F₁ p), degContrib p v e j = ∑ e ∈ L, degContrib p v e j := by
            refine sum_subset (filter_subset _ _) fun e he hne => ?_
            by_contra h
            obtain ⟨u, rfl, hu⟩ := degContrib_cases h
            exact hne (mem_filter.mpr ⟨he, by rw [aE_mk, hu]; exact hA⟩)
        _ = ∑ τ ∈ (F₁ ∪ F₂).filter (fun τ => p v ∈ τ), c τ * typeDegVec τ (p v) j := by
            rw [← hdv, hc, hcd]
        _ = ∑ τ ∈ F₁.filter (fun τ => p v ∈ τ), c τ * typeDegVec τ (p v) j := by
            refine (sum_subset (filter_subset_filter _ subset_union_left) fun τ hτ hτ1 => ?_).symm
            obtain ⟨hτU, hvτ⟩ := mem_filter.mp hτ
            have hτ2 : τ ∈ F₂ := (mem_union.mp hτU).resolve_left
              (fun h => hτ1 (mem_filter.mpr ⟨h, hvτ⟩))
            by_contra h
            have h' : typeDegVec τ (p v) j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
            exact hdisj _ j hA ⟨τ, hτ2, hc2 τ hτ2, le_of_typeDegVec_ne hvτ h'⟩
    · rw [sum_eq_zero, sum_eq_zero]
      · intro τ hτ
        obtain ⟨hτ1, hvτ⟩ := mem_filter.mp hτ
        by_contra h
        have h' : typeDegVec τ (p v) j ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
        exact hA ⟨τ, hτ1, hc1 τ hτ1, le_of_typeDegVec_ne hvτ h'⟩
      · intro e he
        by_contra h
        obtain ⟨u, rfl, hu⟩ := degContrib_cases h
        have := (mem_filter.mp he).2
        rw [aE_mk, hu] at this
        exact hA this
/-! ### Restriction of the host to the pairs of a subfamily -/
section Restrict
variable {V : Type*} [Fintype V] [DecidableEq V]
end Restrict
end PartitionedTriangleAbsorption.BlowupB
