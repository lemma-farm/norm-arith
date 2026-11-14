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

-- ==== Examples.scottnarmstrong__DOZZ.Examples.Example_902049d55b7be745240c_KolmogorovCover ====
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
lemma lintegral_sup_rpow_edist_le_sum_of_le_one (hp : p ≤ 1)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hC : ∀ n, IsCover (ε n) J (C n)) (hC_subset : ∀ n, (C n : Set T) ⊆ J) (hm : m ≤ k) 
    (h_DOZZ_Proofs_lintegral_sup_rpow_edist_le_sum_rpow_of_le_one : ∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T]
      {mΩ : MeasurableSpace Ω} [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNReal}
      {P : MeasureTheory.Measure Ω} {X : T → Ω → E} {C : ℕ → Finset T} {k m : ℕ},
      p ≤ 1 →
        ProbabilityTheory.IsAEKolmogorovProcess X P p q M →
          m ≤ k →
            ∫⁻ (ω : Ω),
                ⨆ (t : ↥(C k)),
                  EDist.edist (X (↑t : T) ω) (X (DOZZ.Proofs.chainingSequence C (↑t : T) k m) ω) ^
                    p ∂P ≤
              ∑ i ∈ Finset.range (k - m),
                ∫⁻ (ω : Ω),
                  ⨆ (t : ↥(C k)),
                    EDist.edist (X (DOZZ.Proofs.chainingSequence C (↑t : T) k (m + i)) ω)
                        (X (DOZZ.Proofs.chainingSequence C (↑t : T) k (m + i + 1)) ω) ^
                      p ∂P)
    (h_DOZZ_Proofs_lintegral_sup_rpow_edist_succ : ∀ {T : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : PseudoEMetricSpace T]
      {mΩ : MeasurableSpace Ω} [inst_1 : PseudoEMetricSpace E] {p q : ℝ} {M : NNReal}
      {P : MeasureTheory.Measure Ω} {X : T → Ω → E} {J : Set T} {C : ℕ → Finset T} {ε : ℕ → NNReal}
      {j k : ℕ},
      ProbabilityTheory.IsAEKolmogorovProcess X P p q M →
        (∀ (n : ℕ), Metric.IsCover (ε n) J (↑(C n) : Set T)) →
          (∀ (n : ℕ), (↑(C n) : Set T) ⊆ J) →
            j < k →
              ∫⁻ (ω : Ω),
                  ⨆ (t : ↥(C k)),
                    EDist.edist (X (DOZZ.Proofs.chainingSequence C (↑t : T) k j) ω)
                        (X (DOZZ.Proofs.chainingSequence C (↑t : T) k (j + 1)) ω) ^
                      p ∂P ≤
                (↑(C (j + 1)).card : ENNReal) * (↑M : ENNReal) * (↑(ε j) : ENNReal) ^ q)
    :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ M * ∑ i ∈ Finset.range (k - m), #(C (m + i + 1)) * (ε (m + i) : ℝ≥0∞) ^ q := by
  refine (h_DOZZ_Proofs_lintegral_sup_rpow_edist_le_sum_rpow_of_le_one hp hX hm).trans ?_
  rw [Finset.mul_sum]
  gcongr with i hi
  refine (h_DOZZ_Proofs_lintegral_sup_rpow_edist_succ hX hC hC_subset ?_).trans_eq (by ring)
  simp only [Finset.mem_range] at hi
  omega

end SecondTerm
end DOZZ.Proofs
