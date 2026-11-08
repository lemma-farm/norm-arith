/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott N. Armstrong

Ported from ASDExplicitGamma-dev/Gaussian/ConcentrationSemigroup.lean,
commit 2c9673f0bcca8062b441989bdc56f87b38715bb8.
Modified for Critical2DKPZ, 2026.
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v9f3b3d2299ad.Critical2DKPZ.Ehrhard.GaussianHeatCenter
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Second derivatives and polynomial closure for Gaussian heat flow -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
open Critical2DKPZ.Gaussian (coordinateDerivative standardGaussianMeasure)
namespace Critical2DKPZ.Ehrhard
theorem contDiff_coordinateDerivative_of_two {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) (i : Fin n) :
    ContDiff ℝ 1 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl
/-- Polynomial bounds through second coordinate derivatives imply the corresponding first-derivative bounds. -/
theorem hasPolynomiallyBoundedCoordinateDerivatives_of_second {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) :
    HasPolynomiallyBoundedCoordinateDerivatives F := by
  rcases hF.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  refine ⟨hF.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2), 2 * C, by positivity, d,
    ?_, ?_⟩
  · intro x
    calc
      |F x| ≤ C * (1 + ‖x‖) ^ d := hzero x
      _ ≤ 2 * C * (1 + ‖x‖) ^ d := by
        have hn : 0 ≤ C * (1 + ‖x‖) ^ d := by positivity
        nlinarith
  · intro i x
    calc
      |F x| + |coordinateDerivative F i x| ≤
          C * (1 + ‖x‖) ^ d + C * (1 + ‖x‖) ^ d := add_le_add (hzero x) (hone i x)
      _ = 2 * C * (1 + ‖x‖) ^ d := by ring
/-- Translating the argument translates the point at which the Fréchet derivative is evaluated. -/
theorem fderiv_translate {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x z : Fin n → ℝ) :
    fderiv ℝ (fun y => F (x + y)) z = fderiv ℝ F (x + z) := by
  have hinner : HasFDerivAt (fun y : Fin n → ℝ => x + y)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) z := by
    exact (hasFDerivAt_const_add_iff x).2 (hasFDerivAt_id z)
  have hcomp := (hF.differentiable_one (x + z)).hasFDerivAt.comp z hinner
  simpa [Function.comp_def] using hcomp.fderiv
/-- Coordinate differentiation commutes with translation of the argument. -/
theorem coordinateDerivative_translate {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x z : Fin n → ℝ) (i : Fin n) :
    coordinateDerivative (fun y => F (x + y)) i z =
      coordinateDerivative F i (x + z) := by
  rw [coordinateDerivative, fderiv_translate hF x z, coordinateDerivative]
/-- Translation preserves polynomial bounds through second coordinate derivatives. -/
theorem hasPolynomiallyBoundedSecond_of_translate {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (fun z => F (x + z)) := by
  rcases hF.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  let B : ℝ := 1 + ‖x‖
  let C' : ℝ := C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hnorm (z : Fin n → ℝ) : 1 + ‖x + z‖ ≤ B * (1 + ‖z‖) := by
    have htriangle := norm_add_le x z
    have hprod : 1 + ‖x‖ + ‖z‖ ≤ (1 + ‖x‖) * (1 + ‖z‖) := by
      nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg z)]
    dsimp [B]
    linarith
  have hcont : ContDiff ℝ 2 (fun z : Fin n → ℝ => F (x + z)) := by
    exact hF.1.comp (contDiff_const.add contDiff_id)
  have hfirst (i : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (fun y => F (x + y)) i z =
        coordinateDerivative F i (x + z) :=
    coordinateDerivative_translate (hF.1.of_le (by norm_num)) x z i
  have hsecond (i j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative (fun y => F (x + y)) i) j z =
        coordinateDerivative (coordinateDerivative F i) j (x + z) := by
    have heq : coordinateDerivative (fun y => F (x + y)) i =
        fun y => coordinateDerivative F i (x + y) := by
      funext y
      exact hfirst i y
    rw [heq]
    exact coordinateDerivative_translate
      (contDiff_coordinateDerivative_of_two hF.1 i) x z j
  refine ⟨hcont, C', hC', d, ?_, ?_, ?_⟩
  · intro z
    calc
      |F (x + z)| ≤ C * (1 + ‖x + z‖) ^ d := hzero _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  · intro i z
    rw [hfirst]
    calc
      |coordinateDerivative F i (x + z)| ≤ C * (1 + ‖x + z‖) ^ d := hone i _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  · intro i j z
    rw [hsecond]
    calc
      |coordinateDerivative (coordinateDerivative F i) j (x + z)| ≤
          C * (1 + ‖x + z‖) ^ d := htwo i j _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
end Critical2DKPZ.Ehrhard
