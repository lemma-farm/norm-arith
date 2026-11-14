module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.CompleteLattice.Group
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.EMetricSpace.PairReduction

-- ==== Examples.scottnarmstrong__DOZZ.Dependencies.vc70287717faf.DOZZ.GFFStructure.MetricChaining ====
public section
/-
Copyright (c) 2025-2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite metric chaining

Adapted from the Brownian-motion formalization of Rémy Degenne and collaborators
(github.com/RemyDegenne/brownian-motion). The nearest-cover chaining construction is deterministic.
The companion finite-supremum and integral inequalities supply the quantitative moment bound; no
sample modification is assumed.
-/
@[expose] public section
open scoped ENNReal NNReal
open _root_.ENNReal _root_.Finset
namespace DOZZ.Proofs
section
open ENNReal
namespace ENNReal

end ENNReal

end
section
variable {α ι : Type*} [CompleteLinearOrder α]
-- Move those next to the ciInf/ciSup versions

end
section
open MeasureTheory _root_.ENNReal DOZZ.Proofs.ENNReal
namespace ENNReal

end ENNReal
end
section
open Metric
variable {E : Type*} {x y : E} {A : Set E} {C C₁ C₂ : Finset E} {ε ε₁ ε₂ : ℝ≥0}
open Classical in
/-- Closest point to `x` in the finite set `s`. -/
noncomputable
def nearestPt [EDist E] (s : Finset E) (x : E) : E :=
  if hs : s.Nonempty then (Finset.exists_min_image s (fun y ↦ edist x y) hs).choose else x

variable [PseudoEMetricSpace E]

section Sequence
variable {ε : ℕ → ℝ≥0} {C : ℕ → Finset E} {k n : ℕ}
noncomputable
def chainingSequenceReverse (C : ℕ → Finset E) (x : E) (k : ℕ) : ℕ → E
  | 0 => x
  | n + 1 => nearestPt (C (k - (n + 1))) (chainingSequenceReverse C x k n)

noncomputable
def chainingSequence (C : ℕ → Finset E) (x : E) (k n : ℕ) : E :=
  if n ≤ k then chainingSequenceReverse C x k (k - n) else x

end Sequence
end
end DOZZ.Proofs

end
end

-- ==== Examples.scottnarmstrong__DOZZ.Examples.Example_5a0e52295ae59981744c_KolmogorovCover ====
/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Kolmogorov moment bounds along finite metric covers

Adapted from `IsKolmogorovProcess.lean` of the Brownian-motion formalization of Rémy Degenne and
collaborators (github.com/RemyDegenne/brownian-motion). These estimates combine the actual process
moment assumption with deterministic nearest-cover chaining. The finite-pair reduction and the
Hölder extension are separate proof layers.
-/
@[expose] public section
open MeasureTheory _root_.ProbabilityTheory _root_.Metric _root_.Finset
open scoped ENNReal NNReal Finset
namespace DOZZ.Proofs
section Aux

end Aux
variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}
section Measurability
variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm
variable {J : Set T}

set_option linter.unusedVariables false in
lemma lintegral_sup_rpow_edist_cover_rescale (hX : IsAEKolmogorovProcess X P p q M) (hJ : J.Finite)
    {C : ℕ → Finset T} {ε₀ : ℝ≥0}
    (hC : ∀ i, IsCover (ε₀ * 2⁻¹ ^ i) J (C i)) (hC_subset : ∀ i, (C i : Set T) ⊆ J)
    (hC_card : ∀ i, #(C i) = coveringNumber (ε₀ * 2⁻¹ ^ i) J)
    {δ : ℝ≥0} (hδ_pos : 0 < δ) (hδ_le : δ ≤ ε₀ * 4)
    {k m : ℕ} (hm₁ : ε₀ * 2⁻¹ ^ m ≤ δ) (hm₂ : δ ≤ ε₀ * 4 * 2⁻¹ ^ m) (hmk : m ≤ k) 
    (h_DOZZ_Proofs_edist_chainingSequence_pow_two_le : ∀ {E : Type u_1} {x y : E} {A : Set E} [inst : PseudoEMetricSpace E] {C : ℕ → Finset E} {k n : ℕ}
      {ε₀ : NNReal},
      (∀ (i : ℕ), Metric.IsCover (ε₀ * 2⁻¹ ^ i) A (↑(C i) : Set E)) →
        (∀ (i : ℕ), (↑(C i) : Set E) ⊆ A) →
          x ∈ C k →
            y ∈ C n →
              ∀ m ≤ k,
                m ≤ n →
                  EDist.edist (DOZZ.Proofs.chainingSequence C x k m)
                      (DOZZ.Proofs.chainingSequence C y n m) ≤
                    EDist.edist x y + (↑ε₀ : ENNReal) * 4 * 2⁻¹ ^ m)
    (h_DOZZ_Proofs_lintegral_sup_rpow_edist_cover_of_dist_le : ∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T]
      {mΩ : MeasurableSpace Ω} [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNReal}
      {P : MeasureTheory.Measure Ω} {X : T → Ω → E} {J : Set T},
      ProbabilityTheory.IsAEKolmogorovProcess X P p q M →
        ∀ {C : Finset T} {ε : NNReal},
          (↑C.card : ℕ∞) = Metric.coveringNumber ε J →
            ∀ {c : ENNReal},
              ∫⁻ (ω : Ω),
                  ⨆ (s : ↥C),
                    ⨆ (t : { t : ↥C // EDist.edist s t ≤ c }),
                      EDist.edist (X (↑s : T) ω) (X (↑(↑t : ↥C) : T) ω) ^ p ∂P ≤
                2 ^ (p + 1) * (↑M : ENNReal) *
                    (2 * c * (↑(Metric.coveringNumber ε J).toNat.log2 : ENNReal)) ^ q *
                  (↑(Metric.coveringNumber ε J) : ENNReal))
    (h_DOZZ_Proofs_chainingSequence_mem : ∀ {E : Type u_1} {x : E} {A : Set E} [inst : PseudoEMetricSpace E] {ε : ℕ → NNReal}
      {C : ℕ → Finset E} {k : ℕ},
      (∀ (i : ℕ), Metric.IsCover (ε i) A (↑(C i) : Set E)) →
        A.Nonempty → x ∈ C k → ∀ n ≤ k, DOZZ.Proofs.chainingSequence C x k n ∈ C n)
    :
    ∫⁻ ω, ⨆ (s : C k) (t : { t : C k // edist s t ≤ δ }),
        edist (X (chainingSequence C s k m) ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ 2 ^ (p + 1) * M
        * (16 * δ * Nat.log2 (coveringNumber (δ/4) J).toNat) ^ q
        * coveringNumber (δ/4) J := by
  refine (Set.eq_empty_or_nonempty J).elim (fun hJe => ?_) (fun hJ' => ?_)
  · have hCk : C k = ∅ :=
      Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp (hJe ▸ hC_subset k))
    have : IsEmpty (C k) := ⟨fun x => by simpa [hCk] using x.2⟩
    simp
  have h4ε₀ : 0 < ε₀ * 4 := lt_of_lt_of_le hδ_pos hδ_le
  have hε₀ : 0 < ε₀ := pos_of_mul_pos_left h4ε₀ (by norm_num)
  simp only [iSup_sigma']
  have hf (p : (s : { s // s ∈ C k }) × { t : { t // t ∈ C k } // edist s t ≤ δ }) :
      edist (chainingSequence C p.1 k m) (chainingSequence C p.2 k m) ≤ ε₀ * 8 * 2⁻¹ ^ m := by
    refine (h_DOZZ_Proofs_edist_chainingSequence_pow_two_le hC hC_subset p.1.2 p.2.1.2 _ hmk hmk).trans ?_
    rw [(show (8 : ℝ≥0∞) = 4 + 4 by norm_num), mul_add, add_mul]
    refine add_le_add_left (p.2.2.trans ?_) _
    have hm₂' : (δ : ℝ≥0∞) ≤ ((ε₀ * 4 * 2⁻¹ ^ m : ℝ≥0) : ℝ≥0∞) := mod_cast hm₂
    simpa [ENNReal.inv_pow] using hm₂'
  let f : (s : C k) × { t : C k // edist s t ≤ δ } →
      (s : C m) × { t : C m // edist s t ≤ ε₀ * 8 * 2⁻¹ ^ m } :=
    fun p => ⟨⟨chainingSequence C p.1 k m, h_DOZZ_Proofs_chainingSequence_mem hC hJ' p.1.2 _ hmk⟩,
      ⟨⟨chainingSequence C p.2 k m, h_DOZZ_Proofs_chainingSequence_mem hC hJ' p.2.1.2 _ hmk⟩, hf _⟩⟩
  refine (lintegral_mono
    (fun ω => iSup_comp_le (fun st => edist (X st.1 ω) (X st.2 ω) ^ p) f)).trans ?_
  simp only [iSup_sigma]
  refine (h_DOZZ_Proofs_lintegral_sup_rpow_edist_cover_of_dist_le hX (hC_card _)).trans ?_
  have hint : coveringNumber (ε₀ * 2⁻¹ ^ m) J ≤ coveringNumber (δ / 4) J := by
    apply coveringNumber_anti
    rw [div_le_iff₀ (by simp)]
    convert hm₂ using 1
    ring
  gcongr _ * _ * (?_ * ?_) ^ q * ?_
  · exact hX.q_pos.le
  · rw [mul_comm _ 8, ← mul_assoc, ← mul_assoc, mul_assoc]
    gcongr
    · norm_num
    · have hm₁' : ((ε₀ * 2⁻¹ ^ m : ℝ≥0) : ℝ≥0∞) ≤ δ := mod_cast hm₁
      simpa [ENNReal.inv_pow] using hm₁'
  · rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    simp only [Nat.cast_le]
    apply Nat.log_mono_right
    apply ENat.toNat_le_toNat hint
    have := IsCover.coveringNumber_le_encard (subset_rfl : J ⊆ J) (by simp) (ε := δ / 4)
    refine ne_top_of_le_ne_top ?_ this
    simpa
  · simpa only [ENat.toENNReal_le]
end FirstTerm
section SecondTerm
variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

end SecondTerm
end DOZZ.Proofs
