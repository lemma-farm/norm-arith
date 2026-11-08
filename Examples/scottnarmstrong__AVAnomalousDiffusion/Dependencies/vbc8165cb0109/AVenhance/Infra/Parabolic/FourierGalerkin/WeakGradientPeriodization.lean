-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Heat.PeriodicCutoff
public import Mathlib
public import Mathlib.MeasureTheory.Group.FundamentalDomain
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Periodizing compact Euclidean tests against the periodic weak gradient

The lattice of integer translations has a compact fundamental cell. Compact support makes the
periodization locally a finite sum, so it retains the smoothness of the original test.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped Pointwise Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
abbrev WeakGradientPeriodization.PeriodLattice :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))
abbrev WeakGradientPeriodization.PeriodTranslations := WeakGradientPeriodization.PeriodLattice.toAddSubgroup
def WeakGradientPeriodization.PeriodCell : Set (Vec 2) :=
  ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 2))
theorem WeakGradientPeriodization.periodTranslation_integerVector (z : WeakGradientPeriodization.PeriodTranslations) :
    ∃ k : Fin 2 → ℤ, (z : Vec 2) = AVenhance.latticeShift k := by
  have hrepr :=
    ((Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ (z : Vec 2)).mp z.property
  have hcoord : ∀ i : Fin 2, ∃ n : ℤ,
      (n : ℝ) = (Pi.basisFun ℝ (Fin 2)).repr (z : Vec 2) i := by
    intro i
    exact Set.mem_range.mp (hrepr i)
  let k : Fin 2 → ℤ := fun i => Classical.choose (hcoord i)
  refine ⟨k, ?_⟩
  funext i
  change (z : Vec 2) i = (k i : ℝ)
  simpa only [k, Pi.basisFun_repr] using (Classical.choose_spec (hcoord i)).symm
noncomputable def WeakGradientPeriodization.periodTranslationIndex (z : WeakGradientPeriodization.PeriodTranslations) : Fin 2 → ℤ :=
  Classical.choose (WeakGradientPeriodization.periodTranslation_integerVector z)
theorem WeakGradientPeriodization.periodTranslationIndex_spec (z : WeakGradientPeriodization.PeriodTranslations) :
    (z : Vec 2) = AVenhance.latticeShift (WeakGradientPeriodization.periodTranslationIndex z) :=
  Classical.choose_spec (WeakGradientPeriodization.periodTranslation_integerVector z)
theorem WeakGradientPeriodization.periodLattice_countable :
    (WeakGradientPeriodization.PeriodLattice : Set (Vec 2)).Countable := by
  have hrange : (WeakGradientPeriodization.PeriodLattice : Set (Vec 2)) = Set.range AVenhance.latticeShift := by
    ext x
    constructor
    · intro hx
      let z : WeakGradientPeriodization.PeriodTranslations := ⟨x, hx⟩
      exact ⟨WeakGradientPeriodization.periodTranslationIndex z, (WeakGradientPeriodization.periodTranslationIndex_spec z).symm⟩
    · rintro ⟨k, rfl⟩
      change AVenhance.latticeShift k ∈
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))
      rw [(Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ]
      intro i
      exact ⟨k i, by simp [AVenhance.latticeShift, Pi.basisFun_repr]⟩
  rw [hrange]
  exact Set.countable_range _
instance WeakGradientPeriodization.periodTranslations_countable : Countable WeakGradientPeriodization.PeriodTranslations :=
  WeakGradientPeriodization.periodLattice_countable.to_subtype
instance WeakGradientPeriodization.periodCell_finiteMeasure :
    IsFiniteMeasure (volume.restrict WeakGradientPeriodization.PeriodCell) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, WeakGradientPeriodization.PeriodCell,
    ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]
end AVenhance.Infra.Parabolic.FourierGalerkin
end
