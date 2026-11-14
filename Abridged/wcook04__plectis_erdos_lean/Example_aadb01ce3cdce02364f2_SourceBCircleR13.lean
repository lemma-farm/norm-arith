import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib

-- ==== Examples.wcook04__plectis_erdos_lean.Examples.Example_aadb01ce3cdce02364f2_SourceBCircleR13 ====
set_option pp.unicode.fun true
/-!
# Uniform complex bound for literal B and the actual cancelled pair

The deliberately simple bound costs a polynomial factor 29*n^2 at radius
1+1/n, rather than a harmonic factor. Its logarithm is still O(log n).
All cancellation identities use the actual canonical U,V and the universal
Omega theorem, not an assumed polynomial inclusion.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial   Finset
open scoped BigOperators


set_option linter.unusedVariables false in
lemma sourceBComplex_inner_bound (n s : ℕ) (hs : s ≤ 13 * n)
    (R : ℝ) (z : ℂ) (hR : 1 < R) (hz : ‖z‖ = R) 
    (h_ErdosProblems_Erdos1049_PaperR13_complex_circle_inverse_denominator_le : ∀ (R : ℝ) (z : ℂ), 1 < R → ‖z‖ = R → ∀ (j : ℕ), 0 < j → ‖(z ^ j - 1)⁻¹‖ ≤ (R - 1)⁻¹)
    (h_ErdosProblems_Erdos1049_PaperR13_complex_negative_power_norm_le_one : ∀ (z : ℂ), 1 ≤ ‖z‖ → ∀ (a : ℕ), ‖z ^ (-(↑a : ℤ))‖ ≤ 1)
    :
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
        exact h_ErdosProblems_Erdos1049_PaperR13_complex_circle_inverse_denominator_le R z hR hz j (mem_Icc.mp hj).1
      _ = _ := by simp
  have hsecond : ‖∑ j ∈ Icc 1 (14 * n), z ^ (-((j * (2 * n + s) : ℕ) : ℤ)) *
      (z ^ j - 1)⁻¹‖ ≤ ((14 * n : ℕ) : ℝ) * (R - 1)⁻¹ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Icc 1 (14 * n), (R - 1)⁻¹ := by
        apply sum_le_sum
        intro j hj
        rw [norm_mul]
        have ha := h_ErdosProblems_Erdos1049_PaperR13_complex_negative_power_norm_le_one z (by rw [hz]; exact hR.le)
          (j * (2 * n + s))
        have hb := h_ErdosProblems_Erdos1049_PaperR13_complex_circle_inverse_denominator_le R z hR hz j (mem_Icc.mp hj).1
        calc
          _ ≤ 1 * (R - 1)⁻¹ := mul_le_mul ha hb (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      _ = _ := by simp
  apply (norm_add_le _ _).trans
  have hc : ((2 * n + s : ℕ) : ℝ) + ((14 * n : ℕ) : ℝ) ≤ ((29 * n : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * n + s + 14 * n ≤ 29 * n by omega)
  have hm := mul_le_mul_of_nonneg_right hc hC
  nlinarith

end ErdosProblems.Erdos1049.PaperR13
