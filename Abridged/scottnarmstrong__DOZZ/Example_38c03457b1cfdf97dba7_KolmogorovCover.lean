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

-- ==== Examples.scottnarmstrong__DOZZ.Examples.Example_38c03457b1cfdf97dba7_KolmogorovCover ====
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


set_option linter.unusedVariables false in
lemma lintegral_sup_rpow_edist_le_card_mul_rpow (hX : IsAEKolmogorovProcess X P p q M)
    {ε : ℝ≥0∞} (C : Finset (T × T)) (hC : ∀ u ∈ C, edist u.1 u.2 ≤ ε) 
    (h_DOZZ_Proofs_Finset_sup_le_sum : ∀ {α : Type u_1} {β : Type} [inst : AddCommMonoid β] [inst_1 : LinearOrder β] [inst_2 : OrderBot β]
      [IsOrderedAddMonoid β] (s : Finset α) (f : α → β), (∀ i ∈ s, 0 ≤ f i) → s.sup f ≤ ∑ a ∈ s, f a)
    :
    ∫⁻ ω, ⨆ u : C, edist (X u.1.1 ω) (X u.1.2 ω) ^ p ∂P
      ≤ #C * M * ε ^ q := calc
  _ = ∫⁻ ω, C.sup (fun u => edist (X u.1 ω) (X u.2 ω) ^ p) ∂P := by
        simp only [iSup_subtype, Finset.sup_eq_iSup]
  _ ≤ ∫⁻ ω, ∑ u ∈ C, edist (X u.1 ω) (X u.2 ω) ^ p ∂P := by gcongr; apply h_DOZZ_Proofs_Finset_sup_le_sum; simp
  _ = ∑ u ∈ C, ∫⁻ ω, edist (X u.1 ω) (X u.2 ω) ^ p ∂P :=
        lintegral_finsetSum' _ (fun _ _ => AEMeasurable.pow_const hX.aemeasurable_edist _)
  _ ≤ ∑ u ∈ C, M * edist u.1 u.2 ^ q := by gcongr; apply hX.kolmogorovCondition
  _ ≤ ∑ u ∈ C, M * ε ^ q := by
    gcongr
    · exact hX.q_pos.le
    · apply hC; assumption
  _ = #C * M * ε ^ q := by simp [mul_assoc]

section FirstTerm
variable {J : Set T}

end FirstTerm
section SecondTerm
variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

end SecondTerm
end DOZZ.Proofs
