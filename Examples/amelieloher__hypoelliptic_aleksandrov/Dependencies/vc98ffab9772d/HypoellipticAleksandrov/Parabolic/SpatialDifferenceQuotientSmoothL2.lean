module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc98ffab9772d.PDEFoundation.Sobolev.Inequalities.SmoothSegment
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Global `L²` control of smooth spatial difference quotients

This file proves the constant-one whole-space estimate needed before local
cutoffs are introduced.
-/
@[expose] public section
open MeasureTheory
private theorem integrable_sq_classicalGradient
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcompact : HasCompactSupport φ) :
    Integrable (fun y => PDE.vecEuclideanNorm (PDE.classicalGradient φ y) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
  have hcomponent : ∀ i : Fin d,
      Integrable (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2)
      (volume : Measure (PDE.Vec d)) := by
    intro i
    have hc : Continuous (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2) :=
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2
    have hs : HasCompactSupport (fun y => ((fderiv ℝ φ y) (PDE.basisVec i)) ^ 2) :=
      (hφcompact.fderiv_apply ℝ (PDE.basisVec i)).comp_left
        (g := fun x : ℝ => x ^ 2) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hs
  simp_rw [PDE.vecEuclideanNorm_sq, PDE.vecNormSq_eq_sum_sq,
    PDE.classicalGradient_apply]
  exact integrable_finsetSum _ fun i _ => hcomponent i
private theorem spatialDifferenceQuotient_sq_le_segmentIntegral
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0) (y : PDE.Vec d) :
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 ≤
      ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2 := by
  let z : PDE.Vec d := h • PDE.basisVec k
  have hbase := PDE.abs_sub_rpow_le_integral_euclideanGradient_mul_distance_rpow
    (p := (2 : ℝ)) (by norm_num) hφ (y + z) y
  have hnormz : PDE.vecEuclideanNorm z = |h| := by
    rw [show z = h • PDE.basisVec k by rfl,
      PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_basisVec]
    simp
  have hbase' : |φ (y + z) - φ y| ^ (2 : ℝ) ≤
      ∫ t in (0 : ℝ)..1,
        (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ) := by
    simpa only [PDE.segmentBlend_eq_add_smul_sub, add_sub_cancel_left, hnormz] using hbase
  have hsq : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  have hdivide : |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 ≤
      (∫ t in (0 : ℝ)..1,
        (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ)) / h ^ 2 :=
    (div_le_div_iff_of_pos_right hsq).mpr hbase'
  rw [← intervalIntegral.integral_div] at hdivide
  have hrewrite : (fun t : ℝ =>
      (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ) / h ^ 2) =
      fun t => PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) ^ 2 := by
    funext t
    rw [Real.rpow_two]
    ring_nf
    rw [sq_abs]
    field_simp
  rw [hrewrite] at hdivide
  have hleft : ((φ (y + z) - φ y) / h) ^ 2 =
      |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 := by
    rw [Real.rpow_two, sq_abs]
    field_simp
  calc
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 =
        ((φ (y + z) - φ y) / h) ^ 2 := by simp only [z]
    _ = |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 := hleft
    _ ≤ ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) ^ 2 := hdivide
    _ = ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm
          (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2 := by
      simp only [z]
