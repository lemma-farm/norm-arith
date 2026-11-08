-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.Construction.Section2FlowRegularityCore
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Pointwise all-order spatial derivative bounds for the §2 flow. -/
@[expose] public section
open Homogenization MeasureTheory
open scoped ContDiff
noncomputable section
namespace AVenhance.Infra.Construction
theorem Section2FlowHigherDerivative.continuous_norm_le_of_ae_le_vecVolume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} {B : ℝ} (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖f x‖ₑ ≤ ENNReal.ofReal B) : ∀ x, ‖f x‖ ≤ B := by
  have hopenPos : (FaaDiBruno.vecVolume 2).IsOpenPosMeasure := by
    unfold FaaDiBruno.vecVolume
    infer_instance
  intro x
  by_contra hx
  have hx' : B < ‖f x‖ := lt_of_not_ge hx
  let U : Set (Vec 2) := {y | B < ‖f y‖}
  have hUopen : IsOpen U := isOpen_lt continuous_const (Continuous.norm hf)
  have hUnonempty : U.Nonempty := ⟨x, hx'⟩
  have hUpos : 0 < (FaaDiBruno.vecVolume 2) U :=
    (hopenPos.open_pos U hUopen hUnonempty).bot_lt
  have hnotU : ∀ᵐ y ∂(FaaDiBruno.vecVolume 2), y ∉ U := by
    filter_upwards [h] with y hy
    intro hyU
    have hle : ENNReal.ofReal ‖f y‖ ≤ ENNReal.ofReal B := by
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using hy
    exact (not_lt_of_ge ((ENNReal.ofReal_le_ofReal_iff hB).mp hle)) hyU
  have hUzero : (FaaDiBruno.vecVolume 2) U = 0 := by
    simpa [ae_iff] using hnotU
  exact (ne_of_gt hUpos) hUzero
end AVenhance.Infra.Construction
end
