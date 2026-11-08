module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! # Absolute convergence from summable expected norms

This is the Tonelli step in the infrared construction. The summability set
is measurable and has full measure; restricting the law to it preserves the
original measure. The sum itself will only be defined on that summability
carrier, so no arbitrary value is assigned to a divergent environment.
-/
open MeasureTheory Filter Set
open scoped ENNReal NNReal MeasureTheory
namespace SubdiffusiveProcess
variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
/-- Summable expected norms imply almost-everywhere absolute summability. -/
theorem ae_summable_norm_of_summable_integral_norm {μ : Measure A} {F : ℕ → A → E}
    (hf : ∀ n, Integrable (F n) μ) (hs : Summable (fun n => ∫ a, ‖F n a‖ ∂μ)) :
    ∀ᵐ a ∂μ, Summable (fun n => ‖F n a‖) := by
  have hm n : AEMeasurable (fun a => ‖F n a‖ₑ) μ := (hf n).1.enorm
  have hfin : (∫⁻ a, ∑' n, ‖F n a‖ₑ ∂μ) ≠ ∞ := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hf _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun a => norm_nonneg (F n a))) hs]
    exact ENNReal.ofReal_ne_top
  refine (ae_lt_top' (AEMeasurable.tsum hm) hfin).mono ?_
  intro a ha
  change Summable (fun n => (‖F n a‖₊ : ℝ))
  rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact ha.ne
variable [MeasurableSpace E] [BorelSpace E]
end SubdiffusiveProcess
