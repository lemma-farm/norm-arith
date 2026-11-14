module

public import Mathlib

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_a72cff481656a335b00a_Smoothing ====
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
/-- The Fourier multiplier `(E f)(θ) = ∑_m e^{imθ} E_m f̂(m)`. -/
noncomputable def fourierMultiplier (E : ℤ → V →L[ℂ] V) (f : ℝ → V) (θ : ℝ) : V :=
  ∑' m : ℤ, multiplierTerm E f m θ

/-- Coefficients with the block `S` removed. -/
noncomputable def tailCoeff (E : ℤ → V →L[ℂ] V) (S : Finset ℤ) (m : ℤ) : V →L[ℂ] V :=
  if m ∈ S then 0 else E m
set_option linter.unusedVariables false in
/-- **Lemma `pc:smoothing`, compactness (in the `C⁰ → C^r` form).** The remainder after the
finite-rank truncation to a finite set `S` of frequencies has `‖(·)^{(j)}‖_∞ ≤ ε_j(S) ‖f‖_∞`,
and `ε_j(S) → 0` as `S` exhausts `ℤ`. Hence `E` is an operator-norm limit of finite-rank
operators `C⁰ → C^r` (when `V` is finite dimensional). -/
theorem smoothing_multiplier_tail (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m) (j : ℕ) 
    (h_Euler2D_fourierMultiplier_iteratedDeriv_le : ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℂ V] [CompleteSpace V]
      (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ},
      (∀ θ ∈ Set.Icc 0 (2 * Real.pi), ‖f θ‖ ≤ M) →
        ∀ {w : ℤ → ℝ},
          (∀ (m : ℤ), ‖E m‖ ≤ w m) →
            (∀ (j : ℕ), Summable fun (m : ℤ) ↦ (1 + |(↑m : ℝ)|) ^ j * w m) →
              ∀ (j : ℕ) (θ : ℝ),
                ‖iteratedDeriv j (Euler2D.fourierMultiplier E f) θ‖ ≤
                  (∑' (m : ℤ), (1 + |(↑m : ℝ)|) ^ j * w m) * M)
    :
    (∀ (S : Finset ℤ) (θ : ℝ), ‖iteratedDeriv j (fourierMultiplier (tailCoeff E S) f) θ‖ ≤
      (∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * (if m ∈ S then 0 else w m)) * M) ∧
    Tendsto (fun S : Finset ℤ => ∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * (if m ∈ S then 0 else w m))
      atTop (𝓝 0) := by
  have hw0 : ∀ m, 0 ≤ w m := fun m => (norm_nonneg _).trans (hw m)
  refine ⟨fun S θ => ?_, ?_⟩
  · apply h_Euler2D_fourierMultiplier_iteratedDeriv_le (tailCoeff E S) hf
    · intro m; unfold tailCoeff; split_ifs
      · simp
      · exact hw m
    · intro i
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hsum i)
      · split_ifs
        · simp
        · exact mul_nonneg (by positivity) (hw0 m)
      · split_ifs
        · simp only [mul_zero]; exact mul_nonneg (by positivity) (hw0 m)
        · exact le_rfl
  · have := tendsto_tsum_compl_atTop_zero (fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m)
    refine this.congr (fun S => ?_)
    refine (tsum_subtype {m : ℤ | m ∉ S} (fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m)).trans
      (tsum_congr (fun m => ?_))
    by_cases hm : m ∈ S
    · simp [hm]
    · simp [hm]
end Euler2D
