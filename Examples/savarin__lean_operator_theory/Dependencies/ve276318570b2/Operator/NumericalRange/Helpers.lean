/-
# Recovered helper lemmas for the numerical range

These lemmas reconstruct identities lost during the accidental deletion.
They support the recovered convexity and spectrum-inclusion proofs.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Basic
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem norm_inv_norm_smul {x : E} (hx : x ≠ 0) :
    ‖((‖x‖ : ℂ)⁻¹) • x‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
theorem inner_sub_smul_one_apply_self (A : E →L[ℂ] E) (l : ℂ)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (A - l • 1) x⟫_ℂ = ⟪x, A x⟫_ℂ - l := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hx]
  norm_num
