module
public import Mathlib
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
set_option autoImplicit false
@[expose] public section
/-!
# Hyperbolic identities and pointwise inequalities

The pointwise analytic ingredients of arXiv:2604.11921v2, Sections 3 and 4.
All hyperbolic functions are the actual real functions from mathlib.
-/
namespace Paper
noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x
theorem sech_pos (x : ℝ) : 0 < sech x := one_div_pos.mpr (Real.cosh_pos x)
theorem sech_le_one (x : ℝ) : sech x ≤ 1 := by
  rw [sech, div_le_one (Real.cosh_pos x)]
  exact Real.one_le_cosh x
theorem sech_sq_pos (x : ℝ) : 0 < sech x ^ 2 := sq_pos_of_pos (sech_pos x)
theorem sech_sq_le_one (x : ℝ) : sech x ^ 2 ≤ 1 := by
  have hp := sech_pos x
  have hl := sech_le_one x
  nlinarith
theorem tanh_sq_add_sech_sq (x : ℝ) : Real.tanh x ^ 2 + sech x ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, sech]
  have h := Real.cosh_sq_sub_sinh_sq x
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp
  nlinarith
theorem sech_fourth_le_one (x : ℝ) : sech x ^ 4 ≤ 1 := by
  simpa using pow_le_pow_left₀ (sech_pos x).le (sech_le_one x) 4
theorem tanh_sq_lt_one (x : ℝ) : Real.tanh x ^ 2 < 1 := by
  have hi := tanh_sq_add_sech_sq x
  have hp := sech_sq_pos x
  nlinarith
theorem tanh_sq_le_one (x : ℝ) : Real.tanh x ^ 2 ≤ 1 := (tanh_sq_lt_one x).le
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (sech x ^ 2) x := by
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x)) using 1
  · ext y
    exact Real.tanh_eq_sinh_div_cosh y
  · dsimp [sech]
    have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
    have h := Real.cosh_sq_sub_sinh_sq x
    field_simp
    nlinarith
theorem hasDerivAt_sech (x : ℝ) :
    HasDerivAt sech (-(Real.tanh x * sech x)) x := by
  convert (hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x)) using 1
  · rfl
  · simp only [sech, Real.tanh_eq_sinh_div_cosh]
    ring
theorem hasDerivAt_sech_sq (x : ℝ) :
    HasDerivAt (fun y => sech y ^ 2) (-2 * Real.tanh x * sech x ^ 2) x := by
  convert (hasDerivAt_sech x).pow 2 using 1
  ring
end Paper
