-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Infra.Torus.FourierCalculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Roots.GradNormSq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v9c979da6a77a.AVenhance.Statements.Roots.SpaceGrad
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
end AVenhance.Infra.Torus
