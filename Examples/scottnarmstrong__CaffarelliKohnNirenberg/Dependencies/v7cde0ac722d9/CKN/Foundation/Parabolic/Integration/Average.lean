-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
set_option autoImplicit false
set_option warningAsError true
/-!
# Integration and averages on parabolic cylinders

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent module records generic average identities and
the product-measure formulas used on balls and parabolic cylinders.

The source-facing scale-invariant quantities are intentionally not defined
here.
-/
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
noncomputable section
namespace CKN.Foundation.Parabolic.Integration
private theorem continuous_vec3EuclideanNorm_sub (x : Vec3) :
    Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
  unfold vec3EuclideanNorm
  fun_prop
private theorem norm_vec3_sub_le_euclideanNorm (x y : Vec3) :
    ‖y - x‖ ≤ vec3EuclideanNorm (y - x) := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |(y - x) i| ≤ vec3EuclideanNorm (y - x)
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg ((y - x) j)) (Finset.mem_univ i)
/-! ### Measures and cylinder Fubini -/
theorem volume_vec3Ball_pos {x : Vec3} {r : ℝ} (hr : 0 < r) :
    0 < volume (vec3Ball x r) := by
  have hopen : IsOpen (vec3Ball x r) := by
    unfold vec3Ball
    exact isOpen_lt (continuous_vec3EuclideanNorm_sub x) continuous_const
  exact hopen.measure_pos volume ⟨x, by simp [vec3EuclideanNorm_zero, hr]⟩
/-- A Euclidean spatial ball has finite volume. -/
theorem volume_vec3Ball_lt_top {x : Vec3} {r : ℝ} :
    volume (vec3Ball x r) < ∞ := by
  have hsub : vec3Ball x r ⊆ Metric.ball x r := by
    intro y hy
    change ‖y - x‖ < r
    exact lt_of_le_of_lt (norm_vec3_sub_le_euclideanNorm x y)
      (by
        change vec3EuclideanNorm (y - x) < r at hy
        exact hy)
  exact (measure_mono hsub).trans_lt
    (measure_ball_lt_top (μ := volume) (x := x) (r := r))
/-- A positive-radius parabolic cylinder has positive volume. -/
theorem volume_parabolicCylinder_pos {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    0 < volume (parabolicCylinder x t r) := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_pos (ne_of_gt (volume_vec3Ball_pos hr))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)))
/-- A parabolic cylinder has finite volume. -/
theorem volume_parabolicCylinder_lt_top {x : Vec3} {t r : ℝ} :
    volume (parabolicCylinder x t r) < ∞ := by
  rw [volume_parabolicCylinder]
  exact ENNReal.mul_lt_top
    (volume_vec3Ball_lt_top (x := x) (r := r))
    ENNReal.ofReal_lt_top
theorem setAverage_norm_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (f : α → E) :
    ‖⨍ x in s, f x ∂μ‖ ≤ ⨍ x in s, ‖f x‖ ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)]
  exact mul_le_mul_of_nonneg_left
    (MeasureTheory.norm_integral_le_integral_norm
      (μ := μ.restrict s) f)
    (inv_nonneg.mpr MeasureTheory.measureReal_nonneg)
end CKN.Foundation.Parabolic.Integration
