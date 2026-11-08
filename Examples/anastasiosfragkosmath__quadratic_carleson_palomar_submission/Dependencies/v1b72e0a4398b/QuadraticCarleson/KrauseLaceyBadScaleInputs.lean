import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyStoppingExtraction
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceySeparatedGeneration
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual bad-scale inputs in the local Krause--Lacey argument

The bad intervals are the actual maximal threshold-ten children for `f`
(the second stopping input is zero). The grouping uses the source's exact
condition `max (2^k₀) |J| = 2^ℓ`, including every smaller child at the base
scale. No cancellation is subtracted from these bad inputs.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
open scoped Classical
/-- The actual source family `B(ℓ)`. -/
noncomputable def badScaleCells (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) : Finset RealInterval :=
  (stoppingChildren S f 0 I₀).filter fun J ↦ max ((2 : ℝ) ^ k₀) J.length = (2 : ℝ) ^ ℓ
/-- The uncancelled bad input `B_ℓ = ∑_{J∈B(ℓ)} f 1_J`. -/
noncomputable def badScaleInput (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) (x : ℝ) : ℂ :=
  ∑ J ∈ badScaleCells S f I₀ k₀ ℓ, J.carrier.indicator f x
theorem badScaleCells_subset (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ ℓ : ℤ) :
    badScaleCells S f I₀ k₀ ℓ ⊆ stoppingChildren S f 0 I₀ :=
  Finset.filter_subset _ _
theorem badScaleCells_pairwiseDisjoint
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ ℓ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    Set.Pairwise (↑(badScaleCells S f I₀ k₀ ℓ) : Set RealInterval)
      (Disjoint on RealInterval.carrier) := by
  intro J hJ K hK hne
  exact stoppingChildren_pairwiseDisjoint f 0 I₀ hlam
    (badScaleCells_subset S f I₀ k₀ ℓ hJ) (badScaleCells_subset S f I₀ k₀ ℓ hK) hne
theorem norm_sum_carrier_indicator_le (T : Finset RealInterval) (f : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑T) (Disjoint on RealInterval.carrier)) (x : ℝ) :
    ‖∑ J ∈ T, J.carrier.indicator f x‖ ≤ ‖f x‖ := by
  by_cases hex : ∃ J ∈ T, x ∈ J.carrier
  · obtain ⟨J, hJ, hxJ⟩ := hex
    rw [Finset.sum_eq_single J]
    · rw [indicator_of_mem hxJ]
    · intro K hK hKJ
      apply indicator_of_notMem
      intro hxK
      exact Set.disjoint_left.mp (hdisj hJ hK hKJ.symm) hxJ hxK
    · intro hn
      exact (hn hJ).elim
  · have hz : ∀ J ∈ T, J.carrier.indicator f x = 0 := by
      intro J hJ
      exact indicator_of_notMem (fun hx ↦ hex ⟨J, hJ, hx⟩) f
    rw [Finset.sum_eq_zero hz, norm_zero]
    exact norm_nonneg _
theorem integrable_badScaleInput (S : Finset RealInterval) {f : ℝ → ℂ}
    (hf : Integrable f) (I₀ : RealInterval) (k₀ ℓ : ℤ) :
    Integrable (badScaleInput S f I₀ k₀ ℓ) := by
  exact integrable_finsetSum _ (fun J _ ↦ hf.indicator J.measurableSet_carrier)
theorem norm_badScaleInput_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ ℓ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (x : ℝ) : ‖badScaleInput S f I₀ k₀ ℓ x‖ ≤ ‖f x‖ :=
  norm_sum_carrier_indicator_le _ f (badScaleCells_pairwiseDisjoint f I₀ k₀ ℓ hlam) x
theorem exists_mem_badScaleCells_of_ne_zero
    {S : Finset RealInterval} {f : ℝ → ℂ} {I₀ : RealInterval} {k₀ ℓ : ℤ} {x : ℝ}
    (hx : badScaleInput S f I₀ k₀ ℓ x ≠ 0) :
    ∃ J ∈ badScaleCells S f I₀ k₀ ℓ, x ∈ J.carrier := by
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro J hJ
  exact indicator_of_notMem (fun hxJ ↦ hn ⟨J, hJ, hxJ⟩) f
/-- Different actual bad scales have disjoint spatial supports. -/
theorem badScale_indices_eq_of_ne_zero
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {ℓ m : ℤ} {x : ℝ}
    (hℓ : badScaleInput S f I₀ k₀ ℓ x ≠ 0) (hm : badScaleInput S f I₀ k₀ m x ≠ 0) :
    ℓ = m := by
  obtain ⟨J, hJ, hxJ⟩ := exists_mem_badScaleCells_of_ne_zero hℓ
  obtain ⟨K, hK, hxK⟩ := exists_mem_badScaleCells_of_ne_zero hm
  have heq : J = K := by
    by_contra hn
    exact Set.disjoint_left.mp (stoppingChildren_pairwiseDisjoint f 0 I₀ hlam
      (badScaleCells_subset S f I₀ k₀ ℓ hJ) (badScaleCells_subset S f I₀ k₀ m hK) hn) hxJ hxK
  have hp : (2 : ℝ) ^ ℓ = (2 : ℝ) ^ m := by
    rw [← (Finset.mem_filter.mp hJ).2, ← (Finset.mem_filter.mp hK).2, heq]
  exact (zpow_right_inj₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp hp
/-- The precise restricted input to an interval's bad-scale piece. -/
noncomputable def intervalBadInput
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval) : ℝ → ℂ :=
  I.centralThird.indicator (badScaleInput S f I₀ k₀ (scale I + 2 - s))
/-- There is no overlap multiplicity in the actual interval bad inputs,
even across different dyadic scales. -/
theorem intervalBadInput_unique_of_ne_zero
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I J : RealInterval} (hI : I ∈ S) (hJ : J ∈ S)
    (hlenI : I.length = (2 : ℝ) ^ (scale I + 2))
    (hlenJ : J.length = (2 : ℝ) ^ (scale J + 2)) {x : ℝ}
    (hxI : intervalBadInput S f I₀ k₀ s scale I x ≠ 0)
    (hxJ : intervalBadInput S f I₀ k₀ s scale J x ≠ 0) : I = J := by
  have hi := Set.indicator_apply_ne_zero.mp hxI
  have hj := Set.indicator_apply_ne_zero.mp hxJ
  have hidx := badScale_indices_eq_of_ne_zero f I₀ k₀ hlam hi.2 hj.2
  have hlen : I.length = J.length := by rw [hlenI, hlenJ, show scale I = scale J by omega]
  by_contra hne
  rcases hlam hI hJ hne with hsub | hsub | hdisj
  · exact hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)
  · exact hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm
  · exact Set.disjoint_left.mp hdisj (I.centralThird_subset_carrier hi.1)
      (J.centralThird_subset_carrier hj.1)
/-- Pointwise no-loss packing for all actual restricted bad inputs. -/
theorem sum_norm_intervalBadInput_le
    {S : Finset RealInterval} (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ S)
    (hlen : ∀ I ∈ N, I.length = (2 : ℝ) ^ (scale I + 2)) (x : ℝ) :
    (∑ I ∈ N, ‖intervalBadInput S f I₀ k₀ s scale I x‖) ≤ ‖f x‖ := by
  by_cases hex : ∃ I ∈ N, intervalBadInput S f I₀ k₀ s scale I x ≠ 0
  · obtain ⟨I, hI, hxI⟩ := hex
    rw [Finset.sum_eq_single I]
    · exact (norm_indicator_le_norm_self _ _).trans
        (norm_badScaleInput_le f I₀ k₀ (scale I + 2 - s) hlam x)
    · intro J hJ hJI
      have hz : intervalBadInput S f I₀ k₀ s scale J x = 0 := by
        by_contra hxJ
        exact hJI (intervalBadInput_unique_of_ne_zero f I₀ k₀ s scale hlam
          (hN hJ) (hN hI) (hlen J hJ) (hlen I hI) hxJ hxI)
      rw [hz, norm_zero]
    · intro hn
      exact (hn hI).elim
  · have hz (I : RealInterval) (hI : I ∈ N) : intervalBadInput S f I₀ k₀ s scale I x = 0 :=
      not_ne_iff.mp fun hx ↦ hex ⟨I, hI, hx⟩
    rw [Finset.sum_eq_zero (fun I hI ↦ by rw [hz I hI, norm_zero])]
    exact norm_nonneg _
/-- Exact no-loss mass packing for all actual interval bad inputs. -/
theorem sum_intervalBadInput_mass_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ S)
    (hlen : ∀ I ∈ N, I.length = (2 : ℝ) ^ (scale I + 2)) :
    (∑ I ∈ N, ∫ x in I.centralThird,
      ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖) ≤ ∫ x, ‖f x‖ := by
  have hint (I : RealInterval) : Integrable (intervalBadInput S f I₀ k₀ s scale I) :=
    (integrable_badScaleInput S hf I₀ k₀ _).indicator I.measurableSet_centralThird
  have hmass (I : RealInterval) :
      (∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖) =
        ∫ x, ‖intervalBadInput S f I₀ k₀ s scale I x‖ := by
    simp only [intervalBadInput, norm_indicator_eq_indicator_norm,
      integral_indicator I.measurableSet_centralThird]
  simp_rw [hmass]
  rw [← integral_finsetSum _ (fun I _ ↦ (hint I).norm)]
  exact integral_mono (integrable_finsetSum _ (fun I _ ↦ (hint I).norm)) hf.norm
    (sum_norm_intervalBadInput_le f I₀ k₀ s scale hlam N hN hlen)
end KrauseLaceyBadScale
end QuadraticCarleson
