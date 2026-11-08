-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus.Calculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus.Fourier
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Fourier coefficients of smooth periodic functions and their derivatives. -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
open scoped ComplexConjugate
local instance avInfraTorusFourierCalculusMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusFourierCalculusMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusFourierCalculusIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
namespace AVenhance.Infra.Torus
/-- The Euclidean representative of the torus character with frequency `k`,
using the sign convention in `mFourierCoeff`. -/
def torusCharacter {d : ℕ} (k : Fin d → ℤ) (x : Vec d) : ℂ :=
  UnitAddTorus.mFourier (-k) (toUnitTorus d x)
theorem torusCharacter_contDiff {d : ℕ} (k : Fin d → ℤ) :
    ContDiff ℝ ⊤ (torusCharacter k) := by
  have hformula : torusCharacter k = fun x : Vec d =>
      ∏ i : Fin d, Complex.exp (2 * Real.pi * Complex.I * (-(k i : ℂ)) * x i) := by
    funext x
    simp only [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      toUnitTorus, fourier_coe_apply]
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    push_cast
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  rw [hformula]
  apply contDiff_prod
  intro i hi
  have hcoord : ContDiff ℝ ⊤ (fun x : Vec d => (x i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℝ) i)
  have hcont := Complex.contDiff_exp.comp
    ((contDiff_const : ContDiff ℝ ⊤ (fun _ : Vec d =>
      2 * Real.pi * Complex.I * (-(k i : ℂ)))).mul hcoord)
  convert hcont using 1
  ext x
  congr 1
theorem torusCharacter_periodic {d : ℕ} (k : Fin d → ℤ) :
    IsZdPeriodic (torusCharacter k) := by
  exact isZdPeriodic_fromUnitTorus (fun x : UnitAddTorus (Fin d) =>
    UnitAddTorus.mFourier (-k) x)
end AVenhance.Infra.Torus
