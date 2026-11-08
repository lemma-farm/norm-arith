-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Mathlib
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vaa235d84621e.Homogenization.Ambient.Basic
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vaa235d84621e.AVenhance.Infra.FaaDiBruno.Seminorm public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vaa235d84621e.AVenhance.Infra.FaaDiBruno.Composition
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
theorem Section2FlowHigherDerivative.continuous_orderedPartial
    {n : ℕ} {f : Vec 2 → Vec 2} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (J : Fin n → Fin 2) :
    Continuous (fun x => FaaDiBruno.orderedPartial n f x J) := by
  have hfN : ContDiff ℝ n f := hf.of_le (by simp)
  have hlift := FaaDiBruno.contDiff_liftVecOne hfN
  have hderiv : Continuous
      (fun z : FaaDiBruno.VecOne 2 =>
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hlift.contDiffAt).continuousAt_iteratedFDeriv (by simp)
  have heval : Continuous
      (fun z : FaaDiBruno.VecOne 2 =>
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z
          (fun j => FaaDiBruno.coordinateVectorOne 2 (J j))) := by
    fun_prop
  have hmap : Continuous (fun x : Vec 2 => WithLp.toLp 1 x) := by fun_prop
  change Continuous
    ((fun z : FaaDiBruno.VecOne 2 =>
      iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z
        (fun j => FaaDiBruno.coordinateVectorOne 2 (J j))) ∘
      (fun x : Vec 2 => WithLp.toLp 1 x))
  exact heval.comp hmap
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
theorem Section2FlowHigherDerivative.continuousVector_norm_le_of_ae_le
    {f : Vec 2 → Vec 2} {B : ℝ} (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(FaaDiBruno.vecVolume 2),
      ‖f x‖ₑ ≤ ENNReal.ofReal B) : ∀ x, ‖f x‖ ≤ B := by
  have hcoord : ∀ i : Fin 2, ∀ x, ‖f x i‖ ≤ B := by
    intro i
    apply Section2FlowHigherDerivative.continuous_norm_le_of_ae_le_vecVolume
      (continuous_apply i |>.comp hf) hB
    filter_upwards [h] with x hx
    have hnorm : ‖f x i‖ ≤ ‖f x‖ := norm_le_pi_norm (f x) i
    have hcomponent : ‖f x i‖ₑ ≤ ‖f x‖ₑ := by
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hnorm
    exact hcomponent.trans hx
  intro x
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  exact hcoord i x
theorem Section2FlowHigherDerivative.orderedPartial_pointwise_of_snorm
    {n : ℕ} {f : Vec 2 → Vec 2} {R C : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hR : 0 < R) (hC : 0 ≤ C)
    (hs : FaaDiBruno.snorm f n R ≤ ENNReal.ofReal C)
    (J : Fin n → Fin 2) (x : Vec 2) :
    ‖FaaDiBruno.orderedPartial n f x J‖ ≤
      C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 := by
  have hderiv := FaaDiBruno.derivativeSup_le_of_snorm_le f hR hs
  have hpartial : FaaDiBruno.partialSup n f J ≤ ENNReal.ofReal
      (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) :=
    (le_iSup_of_le J le_rfl).trans hderiv
  have hess : eLpNormEssSup (fun y => FaaDiBruno.orderedPartial n f y J)
      (FaaDiBruno.vecVolume 2) ≤ ENNReal.ofReal
        (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) := by
    simpa [FaaDiBruno.partialSup] using hpartial
  have hae : ∀ᵐ y ∂(FaaDiBruno.vecVolume 2),
      ‖FaaDiBruno.orderedPartial n f y J‖ₑ ≤ ENNReal.ofReal
        (C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2) :=
    (ae_le_eLpNormEssSup
      (f := fun y => FaaDiBruno.orderedPartial n f y J)
      (μ := FaaDiBruno.vecVolume 2)).mono fun y hy => hy.trans hess
  have hboundNonneg : 0 ≤ C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (by positivity))
      (by positivity)
  have hpoint := Section2FlowHigherDerivative.continuousVector_norm_le_of_ae_le
    (B := C * n.factorial * R ^ n / (n + 1 : ℝ) ^ 2)
    (Section2FlowHigherDerivative.continuous_orderedPartial hf J) hboundNonneg hae
  exact hpoint x
end AVenhance.Infra.Construction
end
