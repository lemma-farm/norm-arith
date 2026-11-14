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

-- ==== Examples.scottnarmstrong__DOZZ.Dependencies.vd3b383d84477.DOZZ.GFFStructure.MetricChaining ====
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

-- ==== Examples.scottnarmstrong__DOZZ.Examples.Example_286c7fee7fa61aa5fead_KolmogorovCover ====
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

end FirstTerm
section SecondTerm
variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}
set_option linter.unusedVariables false in
lemma lintegral_sup_rpow_edist_succ (hX : IsAEKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (ε n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hjk : j < k) 
    (h_DOZZ_Proofs_lintegral_sup_rpow_edist_le_card_mul_rpow : ∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T]
      {mΩ : MeasurableSpace Ω} [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNReal}
      {P : MeasureTheory.Measure Ω} {X : T → Ω → E},
      ProbabilityTheory.IsAEKolmogorovProcess X P p q M →
        ∀ {ε : ENNReal} (C : Finset (T × T)),
          (∀ u ∈ C, EDist.edist u.1 u.2 ≤ ε) →
            ∫⁻ (ω : Ω), ⨆ (u : ↥C), EDist.edist (X (↑u : T × T).1 ω) (X (↑u : T × T).2 ω) ^ p ∂P ≤
              (↑C.card : ENNReal) * (↑M : ENNReal) * ε ^ q)
    (h_DOZZ_Proofs_chainingSequence_chainingSequence : ∀ {E : Type u_1} {x : E} [inst : PseudoEMetricSpace E] {C : ℕ → Finset E} {k : ℕ},
      ∀ n ≤ k,
        ∀ m ≤ n,
          DOZZ.Proofs.chainingSequence C (DOZZ.Proofs.chainingSequence C x k n) n m =
            DOZZ.Proofs.chainingSequence C x k m)
    (h_DOZZ_Proofs_edist_chainingSequence_add_one_self : ∀ {E : Type u_1} {x : E} {A : Set E} [inst : PseudoEMetricSpace E] {ε : ℕ → NNReal}
      {C : ℕ → Finset E} {k : ℕ},
      (∀ (i : ℕ), Metric.IsCover (ε i) A (↑(C i) : Set E)) →
        (∀ (i : ℕ), (↑(C i) : Set E) ⊆ A) →
          x ∈ C (k + 1) →
            EDist.edist (DOZZ.Proofs.chainingSequence C x (k + 1) k) x ≤ (↑(ε k) : ENNReal))
    (h_DOZZ_Proofs_chainingSequence_mem : ∀ {E : Type u_1} {x : E} {A : Set E} [inst : PseudoEMetricSpace E] {ε : ℕ → NNReal}
      {C : ℕ → Finset E} {k : ℕ},
      (∀ (i : ℕ), Metric.IsCover (ε i) A (↑(C i) : Set E)) →
        A.Nonempty → x ∈ C k → ∀ n ≤ k, DOZZ.Proofs.chainingSequence C x k n ∈ C n)
    :
    ∫⁻ ω, ⨆ (t : C k),
        edist (X (chainingSequence C t k j) ω) (X (chainingSequence C t k (j + 1)) ω) ^ p ∂P
      ≤ #(C (j + 1)) * M * ε j ^ q := by
  refine (Set.eq_empty_or_nonempty J).elim (fun hJe => ?_) (fun hJ => ?_)
  · have hCk : C k = ∅ :=
      Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp (hJe ▸ hC_subset k))
    have : IsEmpty (C k) := ⟨fun x => by simpa [hCk] using x.2⟩
    simp
  -- Define the set `C'`, which is called `C` in the informal source
  let f₀ : { x : T // x ∈ C (j + 1) } → T × T := fun x => (chainingSequence C x (j + 1) j, x.1)
  have hf₀ : Function.Injective f₀ := fun x y h => Subtype.ext (congrArg Prod.snd h)
  let C' : Finset (T × T) := (C (j + 1)).attach.map ⟨f₀, hf₀⟩
  have hC' : #C' = #(C (j + 1)) := by simp [C']
  -- First step: reindex from a `C k`-indexed supremum to a `C'`-indexed supremum
  let f (ω : Ω) : { x : T × T // x ∈ C' } → ℝ≥0∞ :=
    fun x => (edist (X x.1.1 ω) (X x.1.2 ω)) ^ p
  let g (ω : Ω) : { x : T // x ∈ C k } → { x : T × T // x ∈ C' } :=
    fun x => ⟨f₀ ⟨chainingSequence C x k (j + 1),
      h_DOZZ_Proofs_chainingSequence_mem hC hJ x.2 (j + 1) (by omega)⟩, by simp [C']⟩
  have hle := lintegral_mono (μ := P) (fun ω => iSup_comp_le (f ω) (g ω))
  simp only [f, g, f₀] at hle
  conv_lhs at hle =>
    right; ext ω; congr; ext x;
      rw [h_DOZZ_Proofs_chainingSequence_chainingSequence (j + 1) (by omega) j (by omega)]
  -- Second step: apply previous results
  refine hle.trans (hC' ▸ h_DOZZ_Proofs_lintegral_sup_rpow_edist_le_card_mul_rpow hX (ε := ε j) C' ?_)
  rintro u hu
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 hu
  simp only [Function.Embedding.coeFn_mk, f₀]
  exact h_DOZZ_Proofs_edist_chainingSequence_add_one_self hC hC_subset u.2

end SecondTerm
end DOZZ.Proofs
