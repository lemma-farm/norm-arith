module

public import Mathlib

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_b1da9cbf15d79a27a000_Smoothing ====
/-!
# Exponentially decaying Fourier multipliers (Lemma `pc:smoothing`)

For a complete complex normed space `V` (for the paper, `V = ℂⁿ` and the `E_m` are matrices),
a `V`-valued function `f` on the circle `ℝ / 2πℤ` has Fourier coefficients
`f̂(m) = (2π)⁻¹ ∫₀^{2π} e^{-imθ} f(θ) dθ`. Given bounded operators `E_m`, the multiplier is
`(E f)(θ) = ∑_m e^{imθ} E_m f̂(m)`.

* `fourierMultiplier_contDiff`, `fourierMultiplier_iteratedDeriv_le`: if
  `‖E_m‖ ≤ w(m)` with `∑_m (1+|m|)^j w(m) < ∞` for all `j`, then `E f` is smooth and
  `‖(E f)^{(j)}‖_∞ ≤ (∑_m (1+|m|)^j w(m)) ‖f‖_∞`; in particular `E : C⁰ → C^r` is bounded for
  every finite `r`.
* `exp_decay_weight_summable`: the weights `C (1+|m|)^k a₀^{|m|}`, `0 < a₀ < 1`, qualify
  (`smoothing_multiplier`).
* `smoothing_multiplier_tail`: the truncations `E_{≤n}` (finite rank when `V` is finite
  dimensional) converge to `E` in the operator norm `C⁰ → C^r`; this is the compactness
  statement of the lemma, here in the `C⁰ → C^r` form.
* `modified_weight`: the same conclusions hold when finitely many `E_m` are changed
  arbitrarily.
* The paper states compactness on the little-Hölder space `c^{1,γ}`; here it is proved as
  operator-norm approximation by finite-rank truncations from `C⁰` into `C^r`
  (`fourierMultiplier_eq_sum_add_tail`, `smoothing_multiplier_tail`), which is the key step
  of the paper's argument. The space `c^{1,γ}` itself is not formalized.
-/
@[expose] public section
open Filter Topology Set MeasureTheory Real Complex
namespace Euler2D
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- Fourier coefficient `f̂(m) = (2π)⁻¹ ∫₀^{2π} e^{-imθ} f(θ) dθ` of a `V`-valued function. -/
noncomputable def fourierCoeffV (f : ℝ → V) (m : ℤ) : V :=
  ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π, cexp (-((m : ℂ) * θ * I)) • f θ
/-- One term `e^{imθ} E_m f̂(m)` of the Fourier multiplier. -/
noncomputable def multiplierTerm (E : ℤ → V →L[ℂ] V) (f : ℝ → V) (m : ℤ) (θ : ℝ) : V :=
  cexp ((m : ℂ) * θ * I) • E m (fourierCoeffV f m)

omit [CompleteSpace V] in
set_option linter.unusedVariables false in
/-- The `j`-th derivative of the `m`-th term is at most `(1+|m|)^j w(m) M`. -/
lemma norm_iteratedFDeriv_multiplierTerm_le (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (j : ℕ) (m : ℤ) (θ : ℝ) 
    (h_Euler2D_norm_cexp_int_mul_I : ∀ (m : ℤ) (θ : ℝ), ‖Complex.exp ((↑m : ℂ) * (↑θ : ℂ) * Complex.I)‖ = 1)
    (h_Euler2D_norm_fourierCoeffV_le : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℂ V] {f : ℝ → V} {M : ℝ},
      (∀ θ ∈ Set.Icc 0 (2 * Real.pi), ‖f θ‖ ≤ M) → ∀ (m : ℤ), ‖Euler2D.fourierCoeffV f m‖ ≤ M)
    (h_Euler2D_iteratedDeriv_cexp_smul : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℂ V] (m : ℤ) (v : V) (j : ℕ)
      (θ : ℝ),
      iteratedDeriv j (fun (θ : ℝ) ↦ Complex.exp ((↑m : ℂ) * (↑θ : ℂ) * Complex.I) • v) θ =
        (((↑m : ℂ) * Complex.I) ^ j * Complex.exp ((↑m : ℂ) * (↑θ : ℂ) * Complex.I)) • v)
    :
    ‖iteratedFDeriv ℝ j (multiplierTerm E f m) θ‖ ≤ (1 + |(m : ℝ)|) ^ j * w m * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf 0 ⟨le_rfl, by positivity⟩)
  have hv : ‖E m (fourierCoeffV f m)‖ ≤ w m * M :=
    (E m).le_opNorm_of_le (h_Euler2D_norm_fourierCoeffV_le hf m) |>.trans
      (mul_le_mul_of_nonneg_right (hw m) hM)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  unfold multiplierTerm
  rw [h_Euler2D_iteratedDeriv_cexp_smul, norm_smul, norm_mul, h_Euler2D_norm_cexp_int_mul_I, mul_one, norm_pow,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
  have h1 : |(m : ℝ)| ^ j ≤ (1 + |(m : ℝ)|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) j
  calc |(m : ℝ)| ^ j * ‖E m (fourierCoeffV f m)‖ ≤ (1 + |(m : ℝ)|) ^ j * (w m * M) :=
        mul_le_mul h1 hv (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Euler2D
