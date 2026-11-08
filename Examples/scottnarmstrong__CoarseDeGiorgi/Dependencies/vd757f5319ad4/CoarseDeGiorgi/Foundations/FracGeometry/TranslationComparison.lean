module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Foundations.FracGeometry.FlatCoordinates
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.vd757f5319ad4.CoarseDeGiorgi.Foundations.FracGeometry.TranslationEnergy
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
namespace CoarseDeGiorgi.Foundations.FracGeometry
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section
/-- Exact powered Lebesgue norm identity for positive finite real exponents. -/
theorem eLpNorm_ofReal_rpow {d : ℕ} {μ : Measure (Vec d)} {r : ℝ} (hr : 0 < r)
    {F : Vec d → ℝ} (hF : Measurable F) :
    eLpNorm F (ENNReal.ofReal r) μ ^ r = ∫⁻ x, ENNReal.ofReal (|F x| ^ r) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top hF.aestronglyMeasurable, ENNReal.toReal_ofReal hr.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr.le]
end
end CoarseDeGiorgi.Foundations.FracGeometry
