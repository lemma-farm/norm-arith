/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeac217a0f20.RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Rescaled test functions in parabolic space

For `φ : ℝ × ℝ³ → ℝ`, a scale `c > 0` and a base point `z`, the rescaled test function is
`φ^c_z(w) = c⁻⁵ φ((w₀ - z₀)/c², (w' - z')/c)` (Hairer, arXiv:1303.5113v4, (2.13)-(3.7)).
The class `B^r` is the set of smooth `φ` supported in the closed unit parabolic ball with
`‖D^k φ‖ ≤ 1` for `k ≤ r`.

We prove the algebra of `parabolicDilate`, the support and integral identities
(`rescaledTestFunction_eq_zero`, `integral_rescaledTestFunction`) and derivative bounds
(`norm_iteratedFDeriv_rescaledTestFunction_le`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
namespace RegularityStructures
@[simp]
theorem parabolicDilate_one (z : ParabolicSpace) : parabolicDilate 1 z = z := by
  simp [parabolicDilate]
theorem parabolicDilate_mul (a b : ℝ) (z : ParabolicSpace) :
    parabolicDilate (a * b) z = parabolicDilate a (parabolicDilate b z) := by
  simp only [parabolicDilate, Prod.mk.injEq, mul_smul]
  exact ⟨by ring, trivial⟩
theorem parabolicDilate_inv_parabolicDilate {c : ℝ} (hc : c ≠ 0) (z : ParabolicSpace) :
    parabolicDilate c⁻¹ (parabolicDilate c z) = z := by
  rw [← parabolicDilate_mul, inv_mul_cancel₀ hc, parabolicDilate_one]
theorem parabolicDilate_parabolicDilate_inv {c : ℝ} (hc : c ≠ 0) (z : ParabolicSpace) :
    parabolicDilate c (parabolicDilate c⁻¹ z) = z := by
  rw [← parabolicDilate_mul, mul_inv_cancel₀ hc, parabolicDilate_one]
theorem measurable_parabolicDilate (c : ℝ) : Measurable (parabolicDilate c) := by
  unfold parabolicDilate
  fun_prop
/-- The parabolic dilation by `d ≠ 0` as a measurable equivalence. -/
noncomputable def parabolicDilateEquiv {d : ℝ} (hd : d ≠ 0) : ParabolicSpace ≃ᵐ ParabolicSpace where
  toFun := parabolicDilate d
  invFun := parabolicDilate d⁻¹
  left_inv := parabolicDilate_inv_parabolicDilate hd
  right_inv := parabolicDilate_parabolicDilate_inv hd
  measurable_toFun := measurable_parabolicDilate d
  measurable_invFun := measurable_parabolicDilate d⁻¹
theorem map_volume_parabolicDilate {d : ℝ} (hd : d ≠ 0) :
    MeasureTheory.Measure.map (parabolicDilate d)
      (MeasureTheory.volume : MeasureTheory.Measure ParabolicSpace) =
      ENNReal.ofReal |(d ^ 5)⁻¹| • MeasureTheory.volume := by
  have h1 : MeasureTheory.Measure.map (fun t : ℝ => d ^ 2 * t) MeasureTheory.volume =
      ENNReal.ofReal |(d ^ 2)⁻¹| • MeasureTheory.volume :=
    Real.map_volume_mul_left (pow_ne_zero 2 hd)
  have h2 : MeasureTheory.Measure.map (fun x : Fin 3 → ℝ => d • x) MeasureTheory.volume =
      ENNReal.ofReal |(d ^ 3)⁻¹| • MeasureTheory.volume := by
    simpa using MeasureTheory.Measure.map_addHaar_smul
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) hd
  have h3 : parabolicDilate d = Prod.map (fun t : ℝ => d ^ 2 * t) (fun x : Fin 3 → ℝ => d • x) :=
    rfl
  rw [MeasureTheory.Measure.volume_eq_prod, h3,
    ← MeasureTheory.Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h1, h2,
    MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul]
  congr 3
  ring
theorem integral_comp_parabolicDilate (φ : ParabolicSpace → ℝ) {d : ℝ} (hd : 0 < d) :
    ∫ w, φ (parabolicDilate d w) = (d ^ 5)⁻¹ * ∫ w, φ w := by
  have hd' : d ≠ 0 := hd.ne'
  have := (parabolicDilateEquiv hd').measurableEmbedding.integral_map (μ := MeasureTheory.volume) φ
  have e : ∫ w, φ (parabolicDilate d w) = ∫ y, φ y ∂(MeasureTheory.Measure.map
      (parabolicDilateEquiv hd') MeasureTheory.volume) := this.symm
  rw [e]
  have : (MeasureTheory.Measure.map (parabolicDilateEquiv hd') MeasureTheory.volume) =
      MeasureTheory.Measure.map (parabolicDilate d) MeasureTheory.volume := rfl
  rw [this, map_volume_parabolicDilate hd', MeasureTheory.integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity), smul_eq_mul]
end RegularityStructures
end
