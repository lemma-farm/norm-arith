/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Constants
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.ClassicalSolution.PeriodiseRegularity
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Torus.HeatKernelIntegrability
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finiteness of the regularised constants

This is item (W3) of Lemma 4.1 of the statement.  The periodised mollifier is bounded and supported
in a compact time strip, so its translates are square-integrable.  The remaining assertions are
obtained from the integrable massive heat kernel, bounded convolution estimates, and the same
`L¹`--`L∞` argument for the covariance.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
namespace Phi43
theorem integrable_periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : Integrable (periodise ρ ε) := by
  obtain ⟨C, hC⟩ := bounded_periodise ρ hρ hε
  obtain ⟨a, b, hab⟩ := periodise_eq_zero_outside_time_interval ρ hρ hε
  let K : Set SpaceTime := Set.Icc a b ×ˢ Set.univ
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hKmeas : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hKon : IntegrableOn (periodise ρ ε) K := by
    apply IntegrableOn.of_bound hKcompact.measure_lt_top
      (measurable_periodise ρ hρ).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hC z
  have hkind : Integrable (K.indicator (periodise ρ ε)) :=
    hKon.integrable_indicator hKmeas
  apply hkind.congr
  refine Filter.Eventually.of_forall fun z => ?_
  by_cases hz : z ∈ K
  · simp [hz]
  · have htime : z.1 < a ∨ b < z.1 := by
      have hnot : z.1 ∉ Set.Icc a b := by
        intro hztime
        exact hz ⟨hztime, Set.mem_univ _⟩
      by_cases hleft : z.1 < a
      · exact Or.inl hleft
      · by_cases hright : b < z.1
        · exact Or.inr hright
        · exact False.elim (hnot ⟨le_of_not_gt hleft, le_of_not_gt hright⟩)
    rw [hab z htime]
    simp [hz]
theorem memLp_mollifierAt (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (z : SpaceTime) :
    MemLp (mollifierAt ρ ε z) 2 := by
  obtain ⟨C, hC⟩ := bounded_periodise ρ hρ hε
  obtain ⟨a, b, hab⟩ := periodise_eq_zero_outside_time_interval ρ hρ hε
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right C 0
  have hCD : C ≤ D := le_max_left C 0
  have hbound : ∀ w, |mollifierAt ρ ε z w| ≤ D := by
    intro w
    exact (hC (z - w)).trans hCD
  have hmeas : Measurable (mollifierAt ρ ε z) := by
    unfold mollifierAt
    exact measurable_periodise ρ hρ |>.comp (measurable_const.sub measurable_id)
  let K : Set SpaceTime :=
    Set.Icc (z.1 - b) (z.1 - a) ×ˢ Set.univ
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hKmeas : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hzero : ∀ w ∉ K, mollifierAt ρ ε z w = 0 := by
    intro w hw
    have hwtime : w.1 ∉ Set.Icc (z.1 - b) (z.1 - a) := by
      intro hwt
      exact hw ⟨hwt, Set.mem_univ _⟩
    have hwout : z.1 - w.1 < a ∨ b < z.1 - w.1 := by
      by_cases hleft : w.1 < z.1 - b
      · exact Or.inr (by linarith)
      · by_cases hright : z.1 - a < w.1
        · exact Or.inl (by linarith)
        · exact False.elim (hwtime ⟨le_of_not_gt hleft, le_of_not_gt hright⟩)
    exact hab (z - w) hwout
  have hsq_on : IntegrableOn (fun w => mollifierAt ρ ε z w ^ 2) K := by
    apply IntegrableOn.of_bound hKcompact.measure_lt_top
      (hmeas.pow_const 2).aestronglyMeasurable (D ^ 2)
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_pow]
    nlinarith [abs_nonneg (mollifierAt ρ ε z w), hbound w]
  have hsq : Integrable (fun w => mollifierAt ρ ε z w ^ 2) := by
    have hind : Integrable (K.indicator (fun w => mollifierAt ρ ε z w ^ 2)) :=
      hsq_on.integrable_indicator hKmeas
    apply hind.congr
    refine Filter.Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ K
    · simp [hw]
    · simp [hw, hzero w hw]
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hsq
end Phi43
end RegularityStructures
end
