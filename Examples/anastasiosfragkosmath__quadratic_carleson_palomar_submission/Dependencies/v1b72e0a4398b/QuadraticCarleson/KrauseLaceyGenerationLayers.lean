import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyStoppingExtraction
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The actual finite minimal-generation decomposition

These are the successive inclusion-minimal layers used in KL18. Their
disjointness and finite exhaustion are proved from laminarity and finiteness.
No relative scale gap is inferred merely from a gap between layer labels.
-/
open Function Set
namespace QuadraticCarleson
namespace KrauseLaceyGenerationLayers
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
/-- The literal inclusion-minimal intervals of a finite collection. -/
noncomputable def minimalLayer (S : Finset RealInterval) : Finset RealInterval := by
  classical
  exact S.filter fun I ↦ ∀ J ∈ S, J.carrier ⊆ I.carrier → J = I
theorem mem_minimalLayer_iff {S : Finset RealInterval} {I : RealInterval} :
    I ∈ minimalLayer S ↔ I ∈ S ∧ ∀ J ∈ S, J.carrier ⊆ I.carrier → J = I := by
  classical
  simp [minimalLayer]
theorem minimalLayer_subset (S : Finset RealInterval) : minimalLayer S ⊆ S := by
  intro I hI
  exact (mem_minimalLayer_iff.mp hI).1
theorem minimalLayer_nonempty {S : Finset RealInterval} (hS : S.Nonempty) :
    (minimalLayer S).Nonempty := by
  obtain ⟨I, hI, hmin⟩ := S.exists_min_image RealInterval.length hS
  refine ⟨I, mem_minimalLayer_iff.mpr ⟨hI, ?_⟩⟩
  intro J hJ hsub
  exact interval_eq_of_carrier_subset_of_length_le hsub (hmin J hJ)
noncomputable def remainingIntervals (S : Finset RealInterval) : ℕ → Finset RealInterval
  | 0 => S
  | n + 1 => by classical exact remainingIntervals S n \ minimalLayer (remainingIntervals S n)
noncomputable def generation (S : Finset RealInterval) (n : ℕ) : Finset RealInterval :=
  minimalLayer (remainingIntervals S n)
theorem remainingIntervals_succ_subset (S : Finset RealInterval) (n : ℕ) :
    remainingIntervals S (n + 1) ⊆ remainingIntervals S n := by
  classical
  exact Finset.sdiff_subset
theorem remainingIntervals_antitone (S : Finset RealInterval) :
    Antitone (remainingIntervals S) :=
  antitone_nat_of_succ_le (remainingIntervals_succ_subset S)
theorem remainingIntervals_subset (S : Finset RealInterval) (n : ℕ) :
    remainingIntervals S n ⊆ S :=
  remainingIntervals_antitone S (Nat.zero_le n)
theorem generation_subset (S : Finset RealInterval) (n : ℕ) : generation S n ⊆ S :=
  (minimalLayer_subset _).trans (remainingIntervals_subset S n)
theorem generations_disjoint (S : Finset RealInterval) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (generation S m) (generation S n) := by
  classical
  wlog hlt : m < n generalizing m n
  · exact (this hmn.symm (by omega)).symm
  apply Finset.disjoint_left.mpr
  intro I hIm hIn
  have hrem : I ∈ remainingIntervals S (m + 1) :=
    remainingIntervals_antitone S (by omega : m + 1 ≤ n) (minimalLayer_subset _ hIn)
  exact (Finset.mem_sdiff.mp hrem).2 hIm
theorem card_remainingIntervals_le (S : Finset RealInterval) (n : ℕ) :
    (remainingIntervals S n).card ≤ S.card - n := by
  classical
  induction n with
  | zero => simp [remainingIntervals]
  | succ n ih =>
    by_cases hnone : remainingIntervals S n = ∅
    · simp [remainingIntervals, hnone, minimalLayer]
    · have hpos := Finset.card_pos.mpr (minimalLayer_nonempty
        (Finset.nonempty_iff_ne_empty.mpr hnone))
      rw [remainingIntervals, Finset.card_sdiff_of_subset (minimalLayer_subset _)]
      omega
theorem remainingIntervals_card_eq_empty (S : Finset RealInterval) :
    remainingIntervals S S.card = ∅ := by
  have h := card_remainingIntervals_le S S.card
  exact Finset.card_eq_zero.mp (by omega)
/-- The finite minimal-generation construction exhausts the input
collection, with an explicit bound on the number of layers. -/
theorem exists_generation_of_mem {S : Finset RealInterval} {I : RealInterval}
    (hI : I ∈ S) : ∃ n < S.card, I ∈ generation S n := by
  classical
  by_contra hn
  push_neg at hn
  have hremain : ∀ n ≤ S.card, I ∈ remainingIntervals S n := by
    intro n
    induction n with
    | zero => intro _; exact hI
    | succ n ih =>
      intro hncard
      exact Finset.mem_sdiff.mpr ⟨ih (by omega), hn n (by omega)⟩
  have h := hremain S.card le_rfl
  rw [remainingIntervals_card_eq_empty] at h
  exact Finset.notMem_empty I h
/-- On a containment chain, the actual minimal-generation labels are
strictly ordered. This is the valid ordering used for maximal prefixes. -/
theorem generation_index_lt_of_proper_subset
    {S : Finset RealInterval} {I J : RealInterval} {m n : ℕ}
    (hI : I ∈ generation S m) (hJ : J ∈ generation S n)
    (hsub : I.carrier ⊆ J.carrier) (hne : I ≠ J) : m < n := by
  by_contra hnot
  have hrem : I ∈ remainingIntervals S n :=
    remainingIntervals_antitone S (by omega : n ≤ m) (minimalLayer_subset _ hI)
  exact hne ((mem_minimalLayer_iff.mp hJ).2 I hrem hsub)
end KrauseLaceyGenerationLayers
end QuadraticCarleson
