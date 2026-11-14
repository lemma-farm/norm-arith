module

public import Mathlib

-- ==== Examples.gmDevi__zeta_7_21_lean.Examples.Example_d7db750f2c514efced17_VLine ====
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
@[expose] public section
set_option linter.style.header false
set_option linter.style.longLine false
/-!
# Theorem U, part 1: vertical-line integrals and the half-integer kernels

General complex-analysis toolkit for `Proofs/Lemma20Upper.lean` (Theorem U of docs/proof.md).
Every declaration of this file is copied **verbatim** from the proved pair project
(https://github.com/gmDevi/zeta2-7-9-lean, `Zeta2Lean/Pair/Proofs/Growth.lean`, same Lean/Mathlib
versions), only the namespace changed; nothing here depends on the window configuration.

* Cauchy's theorem and Cauchy's formula (all orders) for right half-planes, on vertical lines
  (`vline_integral_eq_zero`, `vline_cauchy`, `vline_left`, `vline_higher`), from
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` and differentiation under the
  integral sign (`hasDerivAt_vline_integral`);
* the kernels `kerS s t = ∑_{ν ∈ ℤ} (t - ν - 1/2)^{-s}`: bounded on vertical lines through
  integers (`norm_kerS_vline_le`), exponentially decaying in the upper half-plane (`kerS_decay`,
  Eisenstein `q`-expansion), conjugation-symmetric, holomorphic off the half-integers;
* the Taylor coefficients `acoef` of `(x+ε)^{-i}` and the power-series inverse
  `coeff_inv_C_add_X_pow`; `integral_exp_affine_Ioi`.
-/
open Complex MeasureTheory Filter Topology Set Finset PowerSeries
open scoped Real
noncomputable section
namespace ZetaWindow
namespace L20U
/-! ## Vertical-line integrals -/

/-! ## Half-integer kernels -/
/-- The half-integer points `x_ν = ν + 1/2`. -/
def hpt (ν : ℤ) : ℂ := (ν : ℂ) + 1 / 2
/-- The kernel `K_s(t) = ∑_{ν ∈ ℤ} (t - (ν + 1/2))^{-s}`. -/
def kerS (s : ℕ) (t : ℂ) : ℂ := ∑' ν : ℤ, ((t - hpt ν) ^ s)⁻¹


/-- **Exponential decay** of the kernel in the upper half-plane (q-expansion). -/
theorem kerS_decay {s : ℕ} (hs : 2 ≤ s) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ t : ℂ, 1 ≤ t.im → ‖kerS s t‖ ≤ κ * Real.exp (-2 * π * t.im) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  set ρ₀ : ℝ := Real.exp (-2 * π) with hρ₀
  have hρ₀pos : 0 < ρ₀ := Real.exp_pos _
  have hρ₀lt : ρ₀ < 1 := by
    rw [hρ₀]; exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hsum0 : Summable fun d : ℕ => (d : ℝ) ^ k * ρ₀ ^ d :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_pos hρ₀pos]; exact hρ₀lt)
  set S₀ : ℝ := ∑' d : ℕ, (d : ℝ) ^ k * ρ₀ ^ d
  have hS₀ : 0 ≤ S₀ := tsum_nonneg fun d => by positivity
  refine ⟨(2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀), by positivity, fun t ht => ?_⟩
  have htpos : 0 < (t - 1 / 2).im := by simp; linarith
  set z : UpperHalfPlane := ⟨t - 1 / 2, htpos⟩
  have hz : (z : ℂ) = t - 1 / 2 := rfl
  have hq := EisensteinSeries.qExpansion_identity hk z
  have hker : kerS (k + 1) t = ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) := by
    unfold kerS
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1
    ext n
    simp only [Equiv.neg_apply, hpt, hz, one_div]
    congr 2
    push_cast
    ring
  rw [hker, hq]
  set ρ : ℝ := Real.exp (-2 * π * t.im) with hρ
  have hqn : ‖Complex.exp (2 * π * I * (z : ℂ))‖ = ρ := by
    rw [Complex.norm_exp, hz, hρ]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    norm_num
  have hρle : ρ ≤ ρ₀ := by
    rw [hρ, hρ₀]; apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hρpos : 0 < ρ := Real.exp_pos _
  have hsum1 : Summable fun d : ℕ => ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖ := by
    have : Summable fun d : ℕ => (d : ℝ) ^ k * ρ ^ d :=
      summable_pow_mul_geometric_of_norm_lt_one k
        (by rw [Real.norm_eq_abs, abs_of_pos hρpos]; linarith)
    refine this.congr fun d => ?_
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hqn]
  rw [norm_mul]
  have hcoef : ‖(-2 * (π : ℂ) * I) ^ (k + 1) / (k.factorial : ℂ)‖ =
      (2 * π) ^ (k + 1) / (k.factorial : ℝ) := by
    rw [norm_div, norm_pow, Complex.norm_natCast]
    congr 2
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hcoef, show (2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀) * ρ =
    (2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀ * ρ) by ring]
  have hA : 0 ≤ (2 * π) ^ (k + 1) / (k.factorial : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hA
  refine le_trans (norm_tsum_le_tsum_norm hsum1) ?_
  have hterm : ∀ d : ℕ, ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖ ≤
      (S₀ / ρ₀ * ρ) * 0 + (ρ / ρ₀) * ((d : ℝ) ^ k * ρ₀ ^ d) := by
    intro d
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hqn, mul_zero, zero_add]
    rcases d with _ | d
    · have hk0 : k ≠ 0 := by omega
      simp [hk0]
    · rw [pow_succ, pow_succ]
      have : ρ ^ d ≤ ρ₀ ^ d := pow_le_pow_left₀ hρpos.le hρle d
      have h2 : ((d + 1 : ℕ) : ℝ) ^ k * (ρ ^ d * ρ) ≤ ((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ) := by
        gcongr
      calc ((d + 1 : ℕ) : ℝ) ^ k * (ρ ^ d * ρ) ≤ ((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ) := h2
        _ = ρ / ρ₀ * (((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ₀)) := by field_simp
  calc ∑' d : ℕ, ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖
      ≤ ∑' d : ℕ, ((S₀ / ρ₀ * ρ) * 0 + (ρ / ρ₀) * ((d : ℝ) ^ k * ρ₀ ^ d)) :=
        Summable.tsum_le_tsum hterm hsum1 ((hsum0.mul_left (ρ / ρ₀)).congr fun d => by ring)
    _ = (ρ / ρ₀) * S₀ := by
        simp only [mul_zero, zero_add]
        rw [tsum_mul_left]
    _ = S₀ / ρ₀ * ρ := by ring

end L20U
end ZetaWindow
end
