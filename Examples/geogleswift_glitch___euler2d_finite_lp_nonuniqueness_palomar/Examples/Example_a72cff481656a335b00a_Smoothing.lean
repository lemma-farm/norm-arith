module
public import Mathlib
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
omit [CompleteSpace V] in
/-- `|e^{imθ}| = 1`. -/
lemma norm_cexp_int_mul_I (m : ℤ) (θ : ℝ) : ‖cexp ((m : ℂ) * θ * I)‖ = 1 := by
  rw [Complex.norm_exp]; simp
omit [CompleteSpace V] in
/-- `|e^{-imθ}| = 1`. -/
lemma norm_cexp_neg_int_mul_I (m : ℤ) (θ : ℝ) : ‖cexp (-((m : ℂ) * θ * I))‖ = 1 := by
  rw [Complex.norm_exp]; simp
omit [CompleteSpace V] in
/-- Iterated derivatives of `θ ↦ e^{imθ} v`: `(im)^j e^{imθ} v`. -/
lemma iteratedDeriv_cexp_smul (m : ℤ) (v : V) (j : ℕ) (θ : ℝ) :
    iteratedDeriv j (fun θ : ℝ => cexp ((m : ℂ) * θ * I) • v) θ =
      (((m : ℂ) * I) ^ j * cexp ((m : ℂ) * θ * I)) • v := by
  induction j generalizing θ with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have : iteratedDeriv n (fun θ : ℝ => cexp ((m : ℂ) * θ * I) • v) =
        fun θ : ℝ => (((m : ℂ) * I) ^ n * cexp ((m : ℂ) * θ * I)) • v := funext ih
    rw [this]
    have h1 : HasDerivAt (fun θ : ℝ => cexp ((m : ℂ) * θ * I))
        (cexp ((m : ℂ) * θ * I) * ((m : ℂ) * I)) θ := by
      have h0 : HasDerivAt (fun θ : ℝ => ((m : ℂ) * θ * I)) ((m : ℂ) * I) θ := by
        have := ((Complex.ofRealCLM.hasDerivAt (x := θ)).const_mul (m : ℂ)).mul_const I
        simpa using this
      exact h0.cexp
    have h2 := ((h1.const_mul (((m : ℂ) * I) ^ n)).smul_const v)
    rw [h2.deriv]
    congr 1
    ring
omit [CompleteSpace V] in
/-- `θ ↦ e^{imθ} v` is smooth. -/
lemma contDiff_cexp_smul (m : ℤ) (v : V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun θ : ℝ => cexp ((m : ℂ) * θ * I) • v) := by
  have : ContDiff ℝ n (fun θ : ℝ => cexp ((m : ℂ) * θ * I)) := by
    have h : ContDiff ℝ n (fun θ : ℝ => (m : ℂ) * (θ : ℂ) * I) :=
      (contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const
    exact Complex.contDiff_exp.comp h
  exact this.smul contDiff_const
/-- Fourier coefficient `f̂(m) = (2π)⁻¹ ∫₀^{2π} e^{-imθ} f(θ) dθ` of a `V`-valued function. -/
noncomputable def fourierCoeffV (f : ℝ → V) (m : ℤ) : V :=
  ((2 * π)⁻¹ : ℝ) • ∫ θ in (0 : ℝ)..2 * π, cexp (-((m : ℂ) * θ * I)) • f θ
/-- One term `e^{imθ} E_m f̂(m)` of the Fourier multiplier. -/
noncomputable def multiplierTerm (E : ℤ → V →L[ℂ] V) (f : ℝ → V) (m : ℤ) (θ : ℝ) : V :=
  cexp ((m : ℂ) * θ * I) • E m (fourierCoeffV f m)
/-- The Fourier multiplier `(E f)(θ) = ∑_m e^{imθ} E_m f̂(m)`. -/
noncomputable def fourierMultiplier (E : ℤ → V →L[ℂ] V) (f : ℝ → V) (θ : ℝ) : V :=
  ∑' m : ℤ, multiplierTerm E f m θ
omit [CompleteSpace V] in
/-- `‖f̂(m)‖ ≤ M` whenever `‖f‖ ≤ M` on `[0, 2π]`. -/
lemma norm_fourierCoeffV_le {f : ℝ → V} {M : ℝ} (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M)
    (m : ℤ) : ‖fourierCoeffV f m‖ ≤ M := by
  have hint : ‖∫ θ in (0 : ℝ)..2 * π, cexp (-((m : ℂ) * θ * I)) • f θ‖ ≤ M * |2 * π - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ hθ
    rw [Set.uIoc_of_le (by positivity)] at hθ
    rw [norm_smul, norm_cexp_neg_int_mul_I, one_mul]
    exact hf θ ⟨hθ.1.le, hθ.2⟩
  have hpi : 0 < 2 * π := by positivity
  rw [fourierCoeffV, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpi.le)]
  rw [sub_zero, abs_of_pos hpi] at hint
  calc (2 * π)⁻¹ * ‖_‖ ≤ (2 * π)⁻¹ * (M * (2 * π)) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpi.le)
    _ = M := by field_simp
omit [CompleteSpace V] in
/-- The `j`-th derivative of the `m`-th term is at most `(1+|m|)^j w(m) M`. -/
lemma norm_iteratedFDeriv_multiplierTerm_le (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (j : ℕ) (m : ℤ) (θ : ℝ) :
    ‖iteratedFDeriv ℝ j (multiplierTerm E f m) θ‖ ≤ (1 + |(m : ℝ)|) ^ j * w m * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hf 0 ⟨le_rfl, by positivity⟩)
  have hv : ‖E m (fourierCoeffV f m)‖ ≤ w m * M :=
    (E m).le_opNorm_of_le (norm_fourierCoeffV_le hf m) |>.trans
      (mul_le_mul_of_nonneg_right (hw m) hM)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  unfold multiplierTerm
  rw [iteratedDeriv_cexp_smul, norm_smul, norm_mul, norm_cexp_int_mul_I, mul_one, norm_pow,
    norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
  have h1 : |(m : ℝ)| ^ j ≤ (1 + |(m : ℝ)|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) j
  calc |(m : ℝ)| ^ j * ‖E m (fourierCoeffV f m)‖ ≤ (1 + |(m : ℝ)|) ^ j * (w m * M) :=
        mul_le_mul h1 hv (norm_nonneg _) (by positivity)
    _ = _ := by ring
/-- **Lemma `pc:smoothing`, bound `C⁰ → C^r`.** Under the same hypotheses,
`‖(E f)^{(j)}(θ)‖ ≤ (∑_m (1+|m|)^j w(m)) M` for all `j` and `θ`. -/
theorem fourierMultiplier_iteratedDeriv_le (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m) (j : ℕ) (θ : ℝ) :
    ‖iteratedDeriv j (fourierMultiplier E f) θ‖ ≤
      (∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * w m) * M := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  unfold fourierMultiplier
  rw [iteratedFDeriv_tsum_apply (N := (j : ℕ∞)) (f := fun m θ => multiplierTerm E f m θ)
    (fun m => contDiff_cexp_smul m _)
    (fun k _ => (hsum k).mul_right M)
    (fun k m θ _ => norm_iteratedFDeriv_multiplierTerm_le E hf hw k m θ) le_rfl]
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded ((hsum j).mul_right M).hasSum
    (fun m => norm_iteratedFDeriv_multiplierTerm_le E hf hw j m θ)
/-- Coefficients with the block `S` removed. -/
noncomputable def tailCoeff (E : ℤ → V →L[ℂ] V) (S : Finset ℤ) (m : ℤ) : V →L[ℂ] V :=
  if m ∈ S then 0 else E m
/-- **Lemma `pc:smoothing`, compactness (in the `C⁰ → C^r` form).** The remainder after the
finite-rank truncation to a finite set `S` of frequencies has `‖(·)^{(j)}‖_∞ ≤ ε_j(S) ‖f‖_∞`,
and `ε_j(S) → 0` as `S` exhausts `ℤ`. Hence `E` is an operator-norm limit of finite-rank
operators `C⁰ → C^r` (when `V` is finite dimensional). -/
theorem smoothing_multiplier_tail (E : ℤ → V →L[ℂ] V) {f : ℝ → V} {M : ℝ}
    (hf : ∀ θ ∈ Set.Icc 0 (2 * π), ‖f θ‖ ≤ M) {w : ℤ → ℝ} (hw : ∀ m, ‖E m‖ ≤ w m)
    (hsum : ∀ j : ℕ, Summable fun m : ℤ => (1 + |(m : ℝ)|) ^ j * w m) (j : ℕ) :
    (∀ (S : Finset ℤ) (θ : ℝ), ‖iteratedDeriv j (fourierMultiplier (tailCoeff E S) f) θ‖ ≤
      (∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * (if m ∈ S then 0 else w m)) * M) ∧
    Tendsto (fun S : Finset ℤ => ∑' m : ℤ, (1 + |(m : ℝ)|) ^ j * (if m ∈ S then 0 else w m))
      atTop (𝓝 0) := by
  have hw0 : ∀ m, 0 ≤ w m := fun m => (norm_nonneg _).trans (hw m)
  refine ⟨fun S θ => ?_, ?_⟩
  · apply fourierMultiplier_iteratedDeriv_le (tailCoeff E S) hf
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
