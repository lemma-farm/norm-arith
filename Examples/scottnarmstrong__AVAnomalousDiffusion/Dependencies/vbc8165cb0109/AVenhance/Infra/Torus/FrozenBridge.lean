-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.Torus.FourierCalculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Statements.Roots.GradNormSq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Statements.Roots.SpaceGrad
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Real-valued d = 2 corollaries in the paper carriers. -/
@[expose] public section
noncomputable section
open MeasureTheory
open Homogenization
namespace AVenhance.Infra.Torus
/-- Regard a real-valued Euclidean function as complex-valued. -/
def realToComplex (f : Vec 2 → ℝ) : Vec 2 → ℂ := Complex.ofRealCLM ∘ f
/-- The complex coordinate derivative of the real cast is the cast of the
classical gradient. -/
theorem coordDeriv_realToComplex {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (x : Vec 2) :
    coordDeriv i (realToComplex f) x = (AVenhance.spaceGrad f x i : ℂ) := by
  let z := i.removeNth x
  have hx : i.insertNth (x i) z = x := by
    exact Fin.insertNth_self_removeNth i x
  have hcast : ContDiff ℝ 1 (realToComplex f) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hcomplex :=
    (hcast.differentiable (by simp) (i.insertNth (x i) z)).hasFDerivAt
      |>.comp_hasDerivAt (x i) (Homogenization.hasDerivAt_insertNth i z (x i))
  have hreal :=
    (hf.differentiable (by simp) (i.insertNth (x i) z)).hasFDerivAt
      |>.comp_hasDerivAt (x i) (Homogenization.hasDerivAt_insertNth i z (x i))
  have hrealCast := hreal.ofReal_comp
  have hderiv :
      fderiv ℝ (realToComplex f) (i.insertNth (x i) z) (basisVec i) =
        (fderiv ℝ f (i.insertNth (x i) z) (basisVec i) : ℂ) := by
    calc
      _ = deriv (fun t => realToComplex f (i.insertNth t z)) (x i) := hcomplex.deriv.symm
      _ = (fderiv ℝ f (i.insertNth (x i) z) (basisVec i) : ℂ) := hrealCast.deriv
  rw [hx] at hderiv
  simpa [coordDeriv, AVenhance.spaceGrad, realToComplex] using hderiv
theorem FrozenBridge.realToComplex_periodic {f : Vec 2 → ℝ}
    (hperiodic : AVenhance.IsZ2Periodic f) : IsZdPeriodic (realToComplex f) := by
  intro n x
  have h := (isZdPeriodic_iff_frozen f).2 hperiodic n x
  exact congrArg (fun y : ℝ => (y : ℂ)) h
theorem FrozenBridge.realToComplex_gradient_energy {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    (∫ x in unitCell 2,
      ∑ i : Fin 2, ‖coordDeriv i (realToComplex f) x‖ ^ 2) =
      AVenhance.gradNormSq (AVenhance.spaceGrad f) := by
  calc
    (∫ x in unitCell 2,
      ∑ i : Fin 2, ‖coordDeriv i (realToComplex f) x‖ ^ 2) =
        ∫ x in unitCell 2, Homogenization.vecNormSq (AVenhance.spaceGrad f x) := by
      apply setIntegral_congr_ae (measurableSet_unitCell 2)
      filter_upwards with x _hx
      simp [Homogenization.vecNormSq, Homogenization.vecDot,
        coordDeriv_realToComplex hf, pow_two]
    _ = ∫ x in AVenhance.unitCube, Homogenization.vecNormSq (AVenhance.spaceGrad f x) :=
      integral_unitCell_eq_unitCube _
    _ = AVenhance.gradNormSq (AVenhance.spaceGrad f) := rfl
theorem hasSum_sq_realToComplexGradientFourierCoeff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) :
    HasSum
      (fun k : Fin 2 → ℤ =>
        ∑ i : Fin 2, ‖smoothFourierCoeff (coordDeriv i (realToComplex f)) k‖ ^ 2)
      (AVenhance.gradNormSq (AVenhance.spaceGrad f)) := by
  rw [← FrozenBridge.realToComplex_gradient_energy hf]
  convert hasSum_sq_smoothGradientFourierCoeff
    (f := realToComplex f) (Complex.ofRealCLM.contDiff.comp hf) using 1
  simpa [realToComplex] using (integral_unitCell_gradSq_eq_sum_coord
    (Complex.ofRealCLM.contDiff.comp hf)).symm
/-- Fourier multiplier formula for each component of the real gradient. -/
theorem smoothFourierCoeff_spaceGrad {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hperiodic : AVenhance.IsZ2Periodic f)
    (i : Fin 2) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (fun x => (AVenhance.spaceGrad f x i : ℂ)) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * smoothFourierCoeff (realToComplex f) k := by
  have hderiv : coordDeriv i (realToComplex f) =
      fun x => (AVenhance.spaceGrad f x i : ℂ) := by
    funext x
    exact coordDeriv_realToComplex hf i x
  rw [← hderiv]
  exact smoothFourierCoeff_coordDeriv i (Complex.ofRealCLM.contDiff.comp hf)
    (FrozenBridge.realToComplex_periodic hperiodic) k
end AVenhance.Infra.Torus
