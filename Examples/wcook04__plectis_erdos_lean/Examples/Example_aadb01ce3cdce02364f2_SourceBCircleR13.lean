import Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.SourceOmegaCancellationR13
import Examples.wcook04__plectis_erdos_lean.Dependencies.v5976c22e5df4.ErdosProblems.Erdos1049.GaussianCircleBoundsR12
import Mathlib
set_option pp.unicode.fun true
/-!
# Uniform complex bound for literal B and the actual cancelled pair


The deliberately simple bound costs a polynomial factor 29*n^2 at radius
1+1/n, rather than a harmonic factor. Its logarithm is still O(log n).
All cancellation identities use the actual canonical U,V and the universal
Omega theorem, not an assumed polynomial inclusion.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
lemma complex_circle_denominator_lower (R : ℝ) (z : ℂ) (hR : 1 < R)
    (hz : ‖z‖ = R) (j : ℕ) (hj : 0 < j) :
    R - 1 ≤ ‖z ^ j - 1‖ := by
  have hp : R ≤ R ^ j := by
    simpa only [pow_one] using pow_le_pow_right₀ hR.le (show 1 ≤ j by omega)
  have h := norm_sub_norm_le (z ^ j) (1 : ℂ)
  rw [norm_pow, hz, norm_one] at h
  linarith
lemma complex_circle_inverse_denominator_le (R : ℝ) (z : ℂ) (hR : 1 < R)
    (hz : ‖z‖ = R) (j : ℕ) (hj : 0 < j) :
    ‖(z ^ j - 1)⁻¹‖ ≤ (R - 1)⁻¹ := by
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hR)
    (complex_circle_denominator_lower R z hR hz j hj)
lemma complex_negative_power_norm_le_one (z : ℂ) (hz : 1 ≤ ‖z‖) (a : ℕ) :
    ‖z ^ (-(a : ℤ))‖ ≤ 1 := by
  rw [zpow_neg, zpow_natCast, norm_inv, norm_pow]
  have hp : 1 ≤ ‖z‖ ^ a := one_le_pow₀ hz
  have hb : (1 : ℝ) / ‖z‖ ^ a ≤ 1 := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hp)).mpr
    simpa using hp
  simpa only [one_div] using hb
noncomputable def sourceBComplex (n : ℕ) (z : ℂ) : ℂ :=
  sourceBValue (eval₂RingHom (Int.castRingHom ℂ) z) n
noncomputable def sourceACircleMajorant (n : ℕ) (R : ℝ) : ℝ :=
  ((13 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (40 * n) * R ^ sourceK n
lemma sourceBComplex_inner_bound (n s : ℕ) (hs : s ≤ 13 * n)
    (R : ℝ) (z : ℂ) (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖(∑ j ∈ Icc 1 (2 * n + s), (z ^ j - 1)⁻¹) +
      ∑ j ∈ Icc 1 (14 * n), z ^ (-((j * (2 * n + s) : ℕ) : ℤ)) *
        (z ^ j - 1)⁻¹‖ ≤ ((29 * n : ℕ) : ℝ) * (R - 1)⁻¹ := by
  have hC : 0 ≤ (R - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hR).le
  have hfirst : ‖∑ j ∈ Icc 1 (2 * n + s), (z ^ j - 1)⁻¹‖ ≤
      ((2 * n + s : ℕ) : ℝ) * (R - 1)⁻¹ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Icc 1 (2 * n + s), (R - 1)⁻¹ := by
        apply sum_le_sum
        intro j hj
        exact complex_circle_inverse_denominator_le R z hR hz j (mem_Icc.mp hj).1
      _ = _ := by simp
  have hsecond : ‖∑ j ∈ Icc 1 (14 * n), z ^ (-((j * (2 * n + s) : ℕ) : ℤ)) *
      (z ^ j - 1)⁻¹‖ ≤ ((14 * n : ℕ) : ℝ) * (R - 1)⁻¹ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Icc 1 (14 * n), (R - 1)⁻¹ := by
        apply sum_le_sum
        intro j hj
        rw [norm_mul]
        have ha := complex_negative_power_norm_le_one z (by rw [hz]; exact hR.le)
          (j * (2 * n + s))
        have hb := complex_circle_inverse_denominator_le R z hR hz j (mem_Icc.mp hj).1
        calc
          _ ≤ 1 * (R - 1)⁻¹ := mul_le_mul ha hb (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      _ = _ := by simp
  apply (norm_add_le _ _).trans
  have hc : ((2 * n + s : ℕ) : ℝ) + ((14 * n : ℕ) : ℝ) ≤ ((29 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * n + s + 14 * n ≤ 29 * n by omega)
  have hm := mul_le_mul_of_nonneg_right hc hC
  nlinarith
/-- Literal finite B, uniformly on the complete circle outside its poles. -/
theorem actual_B_complex_circle_le (n : ℕ) (R : ℝ) (z : ℂ)
    (hR : 1 < R) (hz : ‖z‖ = R) :
    ‖sourceBComplex n z‖ ≤ sourceACircleMajorant n R *
      (((29 * n : ℕ) : ℝ) * (R - 1)⁻¹) := by
  classical
  unfold sourceBComplex sourceBValue
  simp only [coe_eval₂RingHom, eval₂_X]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ s ∈ range (13 * n + 1),
        ((2 : ℝ) ^ (40 * n) * R ^ sourceK n) *
          (((29 * n : ℕ) : ℝ) * (R - 1)⁻¹) := by
      apply sum_le_sum
      intro s hs
      have hs' : s ≤ 13 * n := by have := mem_range.mp hs; omega
      rw [norm_mul]
      apply mul_le_mul
        (actual_ASummand_complex_disk_le n s hs' R z hR.le hz.le)
        (sourceBComplex_inner_bound n s hs' R z hR hz)
      · exact norm_nonneg _
      · positivity
    _ = _ := by simp [sourceACircleMajorant, mul_assoc]
end ErdosProblems.Erdos1049.PaperR13
