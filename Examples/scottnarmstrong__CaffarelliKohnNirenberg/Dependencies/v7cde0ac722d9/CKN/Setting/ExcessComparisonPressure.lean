-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.ExcessComparisonCore
set_option autoImplicit false
set_option warningAsError true
/-! Pressure-side comparisons for the Tsai excess quantities. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
private theorem tsaiPsi_le_C3_gamma_of_integrability
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn u (parabolicCylinder z.1 z.2 r) volume)
    (hu3 : IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume) :
    r * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) ≤
      (4 * Real.pi / 3) ^ (-1 / 3 : ℝ) * gamma u z r := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 => ℝ)).symm
  have hL : (L : Vec3 → L2Vec3) = WithLp.toLp 2 := by
    funext v
    exact rfl
  have hLint : IntegrableOn (fun w => L (u w))
      (parabolicCylinder z.1 z.2 r) volume :=
    L.toContinuousLinearMap.integrable_comp hu.integrable
  have hL3 : IntegrableOn (fun w => ‖L (u w)‖ ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume := by
    simpa only [vec3EuclideanNorm_eq_l2, hL] using hu3
  have hJ0 := setAverage_norm_rpow_le (μ := (volume : Measure ParabolicPoint))
    (s := parabolicCylinder z.1 z.2 r) (f := fun w => L (u w)) (p := (3 : ℝ))
    (by norm_num) (volume_parabolicCylinder_pos hr)
    (volume_parabolicCylinder_lt_top (x := z.1) (t := z.2) (r := r)) hLint
    (by simpa [Real.rpow_natCast] using hL3)
  have hmap : L (⨍ w in parabolicCylinder z.1 z.2 r, u w) =
      ⨍ w in parabolicCylinder z.1 z.2 r, L (u w) := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    change L ((volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ •
        ∫ w in parabolicCylinder z.1 z.2 r, u w) =
      (volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ •
        ∫ w in parabolicCylinder z.1 z.2 r, L (u w)
    rw [map_smul, L.integral_comp_comm]
  rw [← hmap] at hJ0
  have hJ1 : ‖L (⨍ w in parabolicCylinder z.1 z.2 r, u w)‖ ^ (3 : ℝ) ≤
      (volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ *
        (∫ w in parabolicCylinder z.1 z.2 r, ‖L (u w)‖ ^ (3 : ℝ)) := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq] at hJ0
    rw [MeasureTheory.setAverage_eq]
    simpa [MeasureTheory.measureReal_def, MeasureTheory.measureReal_restrict_apply_univ,
      smul_eq_mul, div_eq_mul_inv] using hJ0
  have hJ : vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) ^ (3 : ℕ) ≤
      (∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ)) /
        (volume (parabolicCylinder z.1 z.2 r)).toReal := by
    convert hJ1 using 1 <;> simp [vec3EuclideanNorm_eq_l2, hL,
      div_eq_mul_inv]
    all_goals ring
  have hvol : (volume (parabolicCylinder z.1 z.2 r)).toReal =
      (4 * Real.pi / 3) * r ^ 5 := by
    rw [volume_parabolicCylinder, volume_vec3Ball_eq, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hI : 0 ≤ ∫ w in parabolicCylinder z.1 z.2 r,
      vec3EuclideanNorm (u w) ^ (3 : ℕ) :=
    integral_nonneg (fun w => pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
  have hgamma : gamma u z r ^ (3 : ℕ) =
      r ^ (-2 : ℝ) * (∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ)) := by
    rw [gamma_cube_eq u z r hr]
    have h := setIntegral_eq_toReal_setLIntegral_of_nonneg hu3
      (Filter.Eventually.of_forall fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
    have h' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w) ^ (3 : ℕ))).toReal =
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
      congr 1
      apply lintegral_congr
      intro w
      rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
      norm_num [ENNReal.rpow_natCast]
    have hEq := h.trans h'
    rw [hEq]
  have hcube : (r * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w)) ^ (3 : ℕ) ≤
      ((4 * Real.pi / 3) ^ (-1 / 3 : ℝ) * gamma u z r) ^ (3 : ℕ) := by
    rw [mul_pow]
    have hc : ((4 * Real.pi / 3) ^ (-1 / 3 : ℝ)) ^ (3 : ℕ) =
        (4 * Real.pi / 3) ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [mul_pow, hc, hgamma]
    have h := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ r ^ 3)
    rw [hvol] at h
    calc
      r ^ 3 * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) ^ 3 ≤
          r ^ 3 * ((∫ w in parabolicCylinder z.1 z.2 r,
            vec3EuclideanNorm (u w) ^ 3) /
            ((4 * Real.pi / 3) * r ^ 5)) := h
      _ = (4 * Real.pi / 3) ^ (-1 : ℝ) *
          (r ^ (-2 : ℝ) * (∫ w in parabolicCylinder z.1 z.2 r,
            vec3EuclideanNorm (u w) ^ 3)) := by
            rw [Real.rpow_neg (by positivity : 0 ≤ (4 * Real.pi / 3 : ℝ)),
              Real.rpow_neg hr.le]
            norm_num [inv_pow]
            field_simp [ne_of_gt hr, Real.pi_ne_zero]
  have hleft : 0 ≤ r * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) :=
    mul_nonneg hr.le (vec3EuclideanNorm_nonneg _)
  have hgamma0 : 0 ≤ gamma u z r := by unfold gamma; positivity
  have hright : 0 ≤ (4 * Real.pi / 3) ^ (-1 / 3 : ℝ) * gamma u z r :=
    mul_nonneg (by positivity) hgamma0
  exact (pow_le_pow_iff_left₀ hleft hright (by norm_num : (3 : ℕ) ≠ 0)).mp hcube
end CKN
