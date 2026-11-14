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

-- ==== Examples.scottnarmstrong__DOZZ.Examples.Example_58e4df8fa2089dd85e6a_KolmogorovCover ====
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
lemma lintegral_sup_rpow_edist_le_sum_rpow_of_le_one (hp : p ≤ 1)
    (hX : IsAEKolmogorovProcess X P p q M) (hm : m ≤ k) 
    (h_DOZZ_Proofs_Finset_iSup_sum_le : ∀ {α ι : Type} {β : Type u_1} [inst : CompleteLattice α] [inst_1 : AddCommMonoid α]
      [IsOrderedAddMonoid α] {I : Finset ι} (f : ι → β → α),
      ⨆ (b : β), ∑ i ∈ I, f i b ≤ ∑ i ∈ I, ⨆ (b : β), f i b)
    (h_DOZZ_Proofs_ENNReal_rpow_finsetSum_le_finsetSum_rpow : ∀ {p : ℝ} {ι : Type} {I : Finset ι} {f : ι → ENNReal},
      0 < p → p ≤ 1 → (∑ i ∈ I, f i) ^ p ≤ ∑ i ∈ I, f i ^ p)
    (h_DOZZ_Proofs_edist_chainingSequence_le_sum_edist : ∀ {E : Type u_1} {x : E} [inst : PseudoEMetricSpace E] {C : ℕ → Finset E} {k : ℕ} {T : Type u_3}
      [inst_1 : PseudoEMetricSpace T] (f : E → T) {m : ℕ},
      m ≤ k →
        EDist.edist (f x) (f (DOZZ.Proofs.chainingSequence C x k m)) ≤
          ∑ i ∈ Finset.range (k - m),
            EDist.edist (f (DOZZ.Proofs.chainingSequence C x k (m + i)))
              (f (DOZZ.Proofs.chainingSequence C x k (m + i + 1))))
    :
    ∫⁻ ω, ⨆ (t : C k), edist (X t ω) (X (chainingSequence C t k m) ω) ^ p ∂P
      ≤ ∑ i ∈ Finset.range (k - m), ∫⁻ ω, ⨆ (t : C k),
        edist (X (chainingSequence C t k (m + i)) ω)
          (X (chainingSequence C t k (m + i + 1)) ω) ^ p ∂P := by
  rw [← lintegral_finsetSum' _ (fun _ _ => .iSup (fun _ => hX.aemeasurable_edist.pow_const _))]
  gcongr with ω
  refine le_trans ?_ (h_DOZZ_Proofs_Finset_iSup_sum_le _)
  gcongr with t
  refine le_trans ?_ (h_DOZZ_Proofs_ENNReal_rpow_finsetSum_le_finsetSum_rpow hX.p_pos hp)
  gcongr
  · exact hX.p_pos.le
  · exact h_DOZZ_Proofs_edist_chainingSequence_le_sum_edist (X · ω) hm

end SecondTerm
end DOZZ.Proofs
