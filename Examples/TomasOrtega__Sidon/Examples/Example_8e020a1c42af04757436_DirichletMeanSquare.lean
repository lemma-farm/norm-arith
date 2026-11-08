module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic
set_option autoImplicit false
set_option pp.unicode.fun true
@[expose] public section
/-! # Finite mean squares of Dirichlet polynomials -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace Sidon
/-- The additive character at an arbitrary real frequency, without a `2π` factor. -/
def frequencyChar (ω t : ℝ) : ℂ := Complex.exp ((ω : ℂ) * t * Complex.I)
theorem norm_integral_frequencyChar_le {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, frequencyChar ω t‖ ≤ 2 / |ω| := by
  have hc : (ω : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hω) Complex.I_ne_zero
  have heq : (fun t : ℝ => frequencyChar ω t) =
      (fun t : ℝ => Complex.exp (((ω : ℂ) * Complex.I) * t)) := by
    funext t
    unfold frequencyChar
    congr 1
    ring
  rw [heq, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, norm_div, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg ω)
  calc
    _ ≤ ‖Complex.exp (((ω : ℂ) * Complex.I) * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp]
end Sidon
