import Mathlib
/-
# Universal circle symmetrization implies the normal auxiliary product bound

For any operator, the sharp symmetrized estimate on every polynomial forces
an enclosing circle's center into the closed numerical range.  Indeed, if the
center were outside, an affine polynomial separator would have value one at
the center and norm at most `r < 1` on the closed numerical range.  Applying
symmetrization to its powers makes the functional-calculus term tend to zero
by the unconditional Crouzeix--Palencia bound, while the circle auxiliary
remains the identity, a contradiction.

The aligned-circle normal product theorem then supplies the literal sharp
auxiliary product estimate.

## Main declarations

* `circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  proves alignment over a compact nonempty convex control set directly from
  universal symmetrization.
* `circle_center_mem_of_isCompact_nonempty_convex_of_global_polynomial_bound_of_forall_symmetrized_bound`
  retains the earlier finite-calculus interface as a corollary.
* `circle_center_mem_closure_numericalRange_of_global_polynomial_bound_of_forall_symmetrized_bound`
  specializes that result to the closed numerical range.
* `circle_center_mem_closure_numericalRange_of_forall_symmetrized_bound`
  specializes direct center alignment to the closed numerical range.
* `norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound`
  gives a uniform power bound on the polynomial ideal vanishing at the circle
  center.
* `norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound`
  preserves the coupled operator/scalar cancellation for every shifted power.
* `norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound`
  gives the corresponding centered power bound for every polynomial.
* `spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound`
  derives the sharp centered spectral inclusion from those power bounds.
* `spectrum_aeval_subset_closedBall_eval_of_forall_symmetrized_bound`
  translates that inclusion back to the spectrum of `p(A)`.
* `spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound`
  gives the analogous sharp spectral disk around every scalar shift.
* `spectrum_aeval_subset_closedBall_shift_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  discharges center membership from compact convex geometry.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_mem_of_forall_symmetrized_bound`
  converts a shifted disk and center membership to a shifted spectral radius.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  gives the sharp spectral-radius bound after every scalar shift.
* `spectralRadius_aeval_le_polynomialSupNorm_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  records its zero-shift specialization.
* `spectrum_aeval_subset_closedBall_shift_closure_numericalRange_of_forall_symmetrized_bound`
  specializes every shifted disk to the closed numerical range.
* `spectralRadius_aeval_sub_smul_one_le_polynomialSupNorm_sub_C_closure_numericalRange_of_forall_symmetrized_bound`
  gives the corresponding sharp shifted spectral-radius bound.
* `spectralRadius_aeval_le_polynomialSupNorm_closure_numericalRange_of_forall_symmetrized_bound`
  gives its zero-shift consequence.
* `spectrum_subset_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  proves that the compact convex control set itself contains the spectrum.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul`
  proves the sharp product bound without normality when the center value is
  at most `sqrt 2 - 1` times the control norm.
* `norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound`
  extracts the operator-norm estimate obtained from any scalar shift.
* `isKPolynomialSpectralSet_three_of_isCompact_nonempty_convex_of_forall_symmetrized_bound`
  packages universal symmetrization as a constant-three polynomial spectral set.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_shifted_scalar_bound_of_forall_symmetrized_bound`
  exposes an arbitrary scalar shift for optimizing the product estimate.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_half_centered_scalar_bound_of_forall_symmetrized_bound`
  specializes the shift to `p(c) / 2`, eliminating the residual scalar term.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_scalar_bound_of_forall_symmetrized_bound`
  isolates the exact adaptive scalar criterion obtained by centering `p`.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_centered_polynomialSupNorm_le_sub_of_forall_symmetrized_bound`
  proves the complementary sharp near-constant branch.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_one_add_sqrt_two_mul_sq_of_forall_symmetrized_bound`
  gives the resulting product estimate for an arbitrary operator at the
  global Crouzeix--Palencia factor.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_aeval_of_forall_symmetrized_bound`
  gives the sharp product estimate whenever the individual value `p(A)` is
  star-normal.
* `norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal_of_forall_symmetrized_bound`
  specializes the sharp estimate to a star-normal operator.
-/
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.ConvexRunge
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.NormalProduct
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.Crouzeix.SmoothSupportDomain
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Convex
import Examples.savarin__lean_operator_theory.Dependencies.ve276318570b2.Operator.NumericalRange.Nonempty
set_option autoImplicit false
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem polynomialSupNorm_pow_le_of_isCompact
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) (n : ℕ) :
    polynomialSupNorm (p ^ n) K ≤ polynomialSupNorm p K ^ n := by
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_)
    (pow_nonneg (polynomialSupNorm_nonneg p K) n)
  refine Real.iSup_le (fun hz ↦ ?_)
    (pow_nonneg (polynomialSupNorm_nonneg p K) n)
  simp only [Polynomial.eval_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz) n
/-- Universal sharp symmetrization on an enclosing circle, controlled by a
compact nonempty convex set, forces the circle center into that set.  No
independent polynomial-calculus bound is needed: if a separator power `B` is
close to `-1`, its square is close to `1`, while symmetrization of the squared
power would make it close to `-1`. -/
theorem circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
    [Nontrivial E] (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K) :
    c ∈ K := by
  by_contra hc
  obtain ⟨p, r, hr0, hr1, hpc, hpK⟩ :=
    exists_polynomial_separator_of_isCompact_nonempty_convex
      K hcompact hnonempty hconvex hc
  obtain ⟨n, hrn⟩ : ∃ n : ℕ, r ^ n < (1 / 8 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hr1
  let q : Polynomial ℂ := p ^ n
  let B : E →L[ℂ] E := Polynomial.aeval A q
  have hsup : polynomialSupNorm q K ≤ r ^ n := by
    unfold q polynomialSupNorm
    refine Real.iSup_le (fun z ↦ ?_) (pow_nonneg hr0 n)
    refine Real.iSup_le (fun hz ↦ ?_) (pow_nonneg hr0 n)
    simp only [Polynomial.eval_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hpK z hz) n
  have hG : crouzeixPolynomialAuxiliaryOperator A
      (SmoothJordanDomain.ball c R
        ((norm_nonneg (A - c • 1)).trans_lt hA)) q =
      (1 : E →L[ℂ] E) := by
    rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
      A c hA q]
    simp only [q, Polynomial.eval_pow, hpc, one_pow, star_one, one_smul]
  have hBadd : ‖B + (1 : E →L[ℂ] E)‖ ≤ 2 * r ^ n := by
    have h := hsymm q
    rw [hG, star_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hsup (by norm_num))
  have hsup_sq : polynomialSupNorm (q ^ 2) K ≤ (r ^ n) ^ 2 := by
    unfold polynomialSupNorm
    refine Real.iSup_le (fun z ↦ ?_) (sq_nonneg _)
    refine Real.iSup_le (fun hz ↦ ?_) (sq_nonneg _)
    simp only [Polynomial.eval_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_eval_le_polynomialSupNorm q
        (bddAbove_norm_eval_image_of_isCompact q hcompact) hz).trans hsup) 2
  have hG_sq : crouzeixPolynomialAuxiliaryOperator A
      (SmoothJordanDomain.ball c R
        ((norm_nonneg (A - c • 1)).trans_lt hA)) (q ^ 2) =
      (1 : E →L[ℂ] E) := by
    rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
      A c hA (q ^ 2)]
    simp only [q, Polynomial.eval_pow, hpc, one_pow, star_one, one_smul]
  have hBsqadd : ‖B ^ 2 + (1 : E →L[ℂ] E)‖ ≤ 2 * (r ^ n) ^ 2 := by
    have h := hsymm (q ^ 2)
    rw [hG_sq, star_one] at h
    simpa only [B, map_pow] using
      h.trans (mul_le_mul_of_nonneg_left hsup_sq (by norm_num))
  have hBsub : ‖B - (1 : E →L[ℂ] E)‖ ≤ 2 * r ^ n + 2 := by
    calc
      ‖B - (1 : E →L[ℂ] E)‖ =
          ‖(B + 1) - (2 : ℂ) • (1 : E →L[ℂ] E)‖ := by
            congr 1
            module
      _ ≤ ‖B + (1 : E →L[ℂ] E)‖ +
          ‖(2 : ℂ) • (1 : E →L[ℂ] E)‖ := norm_sub_le _ _
      _ ≤ 2 * r ^ n + 2 := by
        rw [norm_smul, norm_one]
        norm_num
        exact hBadd
  have hid : (2 : ℂ) • (1 : E →L[ℂ] E) =
      (B ^ 2 + 1) - (B + 1) * (B - 1) := by
    noncomm_ring
    module
  have htwo : (2 : ℝ) ≤
      ‖B ^ 2 + (1 : E →L[ℂ] E)‖ +
        ‖B + (1 : E →L[ℂ] E)‖ * ‖B - (1 : E →L[ℂ] E)‖ := by
    have hnormtwo : ‖(2 : ℂ) • (1 : E →L[ℂ] E)‖ = 2 := by
      rw [norm_smul, norm_one]
      norm_num
    rw [← hnormtwo, hid]
    exact (norm_sub_le _ _).trans
      (add_le_add_right (norm_mul_le (B + 1) (B - 1)) _)
  have hupper :
      ‖B ^ 2 + (1 : E →L[ℂ] E)‖ +
          ‖B + (1 : E →L[ℂ] E)‖ * ‖B - (1 : E →L[ℂ] E)‖ ≤
        2 * (r ^ n) ^ 2 + (2 * r ^ n) * (2 * r ^ n + 2) := by
    exact add_le_add hBsqadd
      (mul_le_mul hBadd hBsub (norm_nonneg _) (by positivity))
  have hrnpow : 0 ≤ r ^ n := pow_nonneg hr0 n
  nlinarith only [htwo, hupper, hrn, hrnpow]
/-- Universal circle symmetrization makes the functional calculus uniformly
power-bounded on the ideal of polynomials vanishing at the circle center.  If
`p(c) = 0`, every positive power of `p(A)` has norm at most twice the
corresponding power of the sup norm on the compact control set. -/
theorem
    norm_pow_aeval_le_two_mul_pow_polynomialSupNorm_of_eval_eq_zero_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (hpc : Polynomial.eval c p = 0) (n : ℕ) :
    ‖Polynomial.aeval A p ^ (n + 1)‖ ≤
      2 * polynomialSupNorm p K ^ (n + 1) := by
  have hpow := hsymm (p ^ (n + 1))
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA (p ^ (n + 1))] at hpow
  simp only [map_pow, Polynomial.eval_pow, hpc,
    zero_pow (Nat.succ_ne_zero n), star_zero, zero_smul, add_zero] at hpow
  exact hpow.trans (mul_le_mul_of_nonneg_left
    (polynomialSupNorm_pow_le_of_isCompact p hK (n + 1)) (by positivity))
/-- Universal circle symmetrization preserves the operator/scalar coupling
for every positive power after an arbitrary shift `b`.  This is stronger
than separately bounding the two summands and retains the cancellation that
is relevant to the sharp product problem. -/
theorem
    norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) (n : ℕ) :
    ‖(Polynomial.aeval A p - b • (1 : E →L[ℂ] E)) ^ (n + 1) +
        (Polynomial.eval c p - b) ^ (n + 1) •
          (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm (p - Polynomial.C b) K ^ (n + 1) := by
  let q : Polynomial ℂ := p - Polynomial.C b
  have hpow := hsymm (q ^ (n + 1))
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA (q ^ (n + 1)), star_smul, star_one, star_star] at hpow
  have hbound := hpow.trans (mul_le_mul_of_nonneg_left
    (polynomialSupNorm_pow_le_of_isCompact q hK (n + 1)) (by positivity))
  simpa only [q, map_pow, map_sub, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_C] using hbound
/-- Universal circle symmetrization uniformly power-bounds the centered
functional calculus.  For every polynomial `p`, positive powers of
`p(A) - p(c)I` are controlled by twice the corresponding power of the sup
norm of `p - p(c)` on the compact control set. -/
theorem
    norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (n : ℕ) :
    ‖(Polynomial.aeval A p -
        Polynomial.eval c p • (1 : E →L[ℂ] E)) ^ (n + 1)‖ ≤
      2 * polynomialSupNorm
        (p - Polynomial.C (Polynomial.eval c p)) K ^ (n + 1) := by
  have hpow :=
    norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
      A c hA hK hsymm p (Polynomial.eval c p) n
  simpa only [sub_self, zero_pow (Nat.succ_ne_zero n), zero_smul,
    add_zero] using hpow
/-- Universal circle symmetrization alone confines the spectrum of the
centered value `p(A) - p(c)I` to the disk whose radius is the sup norm of
`p - p(c)` on the compact control set.  No independent global
polynomial-calculus estimate is assumed; the zero Hilbert space has empty
spectrum. -/
theorem
    spectrum_aeval_sub_eval_smul_one_subset_closedBall_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) :
    spectrum ℂ (Polynomial.aeval A p -
        Polynomial.eval c p • (1 : E →L[ℂ] E)) ⊆
      Metric.closedBall 0
        (polynomialSupNorm (p - Polynomial.C (Polynomial.eval c p)) K) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let _ := hE
  let T : E →L[ℂ] E := Polynomial.aeval A p -
    Polynomial.eval c p • (1 : E →L[ℂ] E)
  let m : ℝ := polynomialSupNorm
    (p - Polynomial.C (Polynomial.eval c p)) K
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hzm
  have hm : 0 ≤ m := polynomialSupNorm_nonneg _ _
  have hmz : m < ‖z‖ := lt_of_not_ge hzm
  have hzpos : 0 < ‖z‖ := hm.trans_lt hmz
  have hratio_nonneg : 0 ≤ m / ‖z‖ := div_nonneg hm hzpos.le
  have hratio_lt_one : m / ‖z‖ < 1 := (div_lt_one hzpos).2 hmz
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (m / ‖z‖) ^ n < (1 / 2 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hratio_lt_one
  have hratio_succ : 2 * (m / ‖z‖) ^ (n + 1) < 1 := by
    have hratio_le_one : m / ‖z‖ ≤ 1 := hratio_lt_one.le
    have hpow_succ : (m / ‖z‖) ^ (n + 1) ≤ (m / ‖z‖) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hratio_nonneg n) hratio_le_one
    nlinarith only [hn, hpow_succ]
  have hzpow_mem : z ^ (n + 1) ∈ spectrum ℂ (T ^ (n + 1)) :=
    spectrum.pow_mem_pow T (n + 1) hz
  have hzpow_le : ‖z‖ ^ (n + 1) ≤ ‖T ^ (n + 1)‖ := by
    simpa only [norm_pow] using spectrum.norm_le_norm_of_mem hzpow_mem
  have hTpow : ‖T ^ (n + 1)‖ ≤ 2 * m ^ (n + 1) := by
    simpa only [T, m] using
      norm_pow_aeval_sub_eval_smul_one_le_two_mul_pow_polynomialSupNorm_sub_C_of_forall_symmetrized_bound
        A c hA hK hsymm p n
  have hstrict : 2 * m ^ (n + 1) < ‖z‖ ^ (n + 1) := by
    calc
      2 * m ^ (n + 1) =
          (2 * (m / ‖z‖) ^ (n + 1)) * ‖z‖ ^ (n + 1) := by
            rw [div_pow]
            field_simp
      _ < 1 * ‖z‖ ^ (n + 1) :=
        mul_lt_mul_of_pos_right hratio_succ (pow_pos hzpos (n + 1))
      _ = ‖z‖ ^ (n + 1) := one_mul _
  exact (not_lt_of_ge (hzpow_le.trans hTpow)) hstrict
/-- If the circle center belongs to the compact control set, the coupled
shifted moments force `spectrum p(A)` into the sharp disk around every scalar
`b`, with radius `sup_K |p-b|`.  The proof keeps the shifted scalar power
inside the moment and lets its norm be absorbed asymptotically; the zero
Hilbert space is handled by its empty spectrum. -/
theorem spectrum_aeval_subset_closedBall_shift_of_mem_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (hK : IsCompact K) (hc : c ∈ K)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    spectrum ℂ (Polynomial.aeval A p) ⊆
      Metric.closedBall b (polynomialSupNorm (p - Polynomial.C b) K) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let _ := hE
  let T : E →L[ℂ] E := Polynomial.aeval A p -
    b • (1 : E →L[ℂ] E)
  let a : ℂ := Polynomial.eval c p - b
  let m : ℝ := polynomialSupNorm (p - Polynomial.C b) K
  have ha : ‖a‖ ≤ m := by
    have h := norm_eval_le_polynomialSupNorm (p - Polynomial.C b)
      (bddAbove_norm_eval_image_of_isCompact (p - Polynomial.C b) hK) hc
    simpa only [a, m, Polynomial.eval_sub, Polynomial.eval_C] using h
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  let w : ℂ := z - b
  have hw : w ∈ spectrum ℂ T := by
    have hshift : spectrum ℂ T =
        spectrum ℂ (Polynomial.aeval A p) - ({b} : Set ℂ) := by
      dsimp only [T]
      rw [← Algebra.algebraMap_eq_smul_one,
        ← spectrum.sub_singleton_eq]
    rw [hshift]
    exact ⟨z, hz, b, Set.mem_singleton b, rfl⟩
  by_contra hwm
  have hm : 0 ≤ m := polynomialSupNorm_nonneg _ _
  have hmw : m < ‖w‖ := lt_of_not_ge hwm
  have hwpos : 0 < ‖w‖ := hm.trans_lt hmw
  have hratio_nonneg : 0 ≤ m / ‖w‖ := div_nonneg hm hwpos.le
  have hratio_lt_one : m / ‖w‖ < 1 := (div_lt_one hwpos).2 hmw
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (m / ‖w‖) ^ n < (1 / 3 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hratio_lt_one
  have hratio_succ : 3 * (m / ‖w‖) ^ (n + 1) < 1 := by
    have hratio_le_one : m / ‖w‖ ≤ 1 := hratio_lt_one.le
    have hpow_succ : (m / ‖w‖) ^ (n + 1) ≤ (m / ‖w‖) ^ n := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hratio_nonneg n) hratio_le_one
    nlinarith only [hn, hpow_succ]
  have hwpow_mem : w ^ (n + 1) ∈ spectrum ℂ (T ^ (n + 1)) :=
    spectrum.pow_mem_pow T (n + 1) hw
  have hadd_mem : w ^ (n + 1) + a ^ (n + 1) ∈
      spectrum ℂ (T ^ (n + 1) +
        a ^ (n + 1) • (1 : E →L[ℂ] E)) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq]
    exact ⟨w ^ (n + 1), hwpow_mem, a ^ (n + 1),
      Set.mem_singleton _, rfl⟩
  have hadd_le : ‖w ^ (n + 1) + a ^ (n + 1)‖ ≤
      ‖T ^ (n + 1) + a ^ (n + 1) • (1 : E →L[ℂ] E)‖ :=
    spectrum.norm_le_norm_of_mem hadd_mem
  have hmoment : ‖T ^ (n + 1) +
      a ^ (n + 1) • (1 : E →L[ℂ] E)‖ ≤ 2 * m ^ (n + 1) := by
    simpa only [T, a, m] using
      norm_shifted_aeval_pow_add_shifted_eval_pow_smul_one_le_two_mul_pow_polynomialSupNorm_of_forall_symmetrized_bound
        A c hA hK hsymm p b n
  have hapow : ‖a‖ ^ (n + 1) ≤ m ^ (n + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ha (n + 1)
  have hwpow_le : ‖w‖ ^ (n + 1) ≤ 3 * m ^ (n + 1) := by
    calc
      ‖w‖ ^ (n + 1) = ‖w ^ (n + 1)‖ := (norm_pow w (n + 1)).symm
      _ = ‖(w ^ (n + 1) + a ^ (n + 1)) - a ^ (n + 1)‖ := by
        rw [add_sub_cancel_right]
      _ ≤ ‖w ^ (n + 1) + a ^ (n + 1)‖ + ‖a ^ (n + 1)‖ :=
        norm_sub_le _ _
      _ ≤ 2 * m ^ (n + 1) + m ^ (n + 1) := by
        simpa only [norm_pow] using add_le_add (hadd_le.trans hmoment) hapow
      _ = 3 * m ^ (n + 1) := by ring
  have hstrict : 3 * m ^ (n + 1) < ‖w‖ ^ (n + 1) := by
    calc
      3 * m ^ (n + 1) =
          (3 * (m / ‖w‖) ^ (n + 1)) * ‖w‖ ^ (n + 1) := by
            rw [div_pow]
            field_simp
      _ < 1 * ‖w‖ ^ (n + 1) :=
        mul_lt_mul_of_pos_right hratio_succ (pow_pos hwpos (n + 1))
      _ = ‖w‖ ^ (n + 1) := one_mul _
  exact (not_lt_of_ge hwpow_le) hstrict
/-- The sharp auxiliary product bound holds without any normality assumption
whenever the center value is small: if `|p(c)| ≤ (sqrt 2 - 1) m`, the
same-polynomial symmetrized estimate bounds `‖p(A)‖` by `2m + |p(c)|`, and the
identity `(sqrt 2 - 1)^2 + 2 (sqrt 2 - 1) = 1` closes the product estimate. -/
theorem
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_eval_center_le_sqrt_two_sub_one_mul
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ} (p : Polynomial ℂ)
    (hsymm :
      ‖Polynomial.aeval A p +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) p)‖ ≤
        2 * polynomialSupNorm p K)
    (hsmall : ‖Polynomial.eval c p‖ ≤
      (Real.sqrt 2 - 1) * polynomialSupNorm p K) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p K ^ 2 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (A - c • 1)).trans_lt hA)) p = 0 :=
      Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact sq_nonneg _
  let _ := hE
  let m : ℝ := polynomialSupNorm p K
  let a : ℝ := ‖Polynomial.eval c p‖
  have hm : 0 ≤ m := polynomialSupNorm_nonneg p K
  have ha : 0 ≤ a := norm_nonneg _
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk : 2 * (Real.sqrt 2 - 1) + (Real.sqrt 2 - 1) ^ 2 = 1 := by
    nlinarith only [hsqrt]
  have hsym := hsymm
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA p, star_smul, star_one, star_star] at hsym
  have hpA : ‖Polynomial.aeval A p‖ ≤ 2 * m + a := by
    calc
      ‖Polynomial.aeval A p‖ =
          ‖(Polynomial.aeval A p +
            Polynomial.eval c p • (1 : E →L[ℂ] E)) -
              Polynomial.eval c p • (1 : E →L[ℂ] E)‖ := by
            rw [add_sub_cancel_right]
      _ ≤ ‖Polynomial.aeval A p +
            Polynomial.eval c p • (1 : E →L[ℂ] E)‖ +
          ‖Polynomial.eval c p • (1 : E →L[ℂ] E)‖ := norm_sub_le _ _
      _ ≤ 2 * m + a := by
        rw [norm_smul, norm_one, mul_one]
        simpa only [m, a] using add_le_add hsym (le_refl a)
  have hlinear : 2 * m * a ≤
      2 * m * ((Real.sqrt 2 - 1) * m) :=
    mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num) hm)
  have hsquare : a ^ 2 ≤ ((Real.sqrt 2 - 1) * m) ^ 2 :=
    pow_le_pow_left₀ ha hsmall 2
  have hfactor : (2 * m + a) * a ≤ m ^ 2 := by
    calc
      (2 * m + a) * a = 2 * m * a + a ^ 2 := by ring
      _ ≤ 2 * m * ((Real.sqrt 2 - 1) * m) +
          ((Real.sqrt 2 - 1) * m) ^ 2 := add_le_add hlinear hsquare
      _ = (2 * (Real.sqrt 2 - 1) + (Real.sqrt 2 - 1) ^ 2) * m ^ 2 := by ring
      _ = m ^ 2 := by rw [hk, one_mul]
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA p]
  calc
    ‖Polynomial.aeval A p *
        (star (Polynomial.eval c p) • (1 : E →L[ℂ] E))‖ ≤
        ‖Polynomial.aeval A p‖ *
          ‖star (Polynomial.eval c p) • (1 : E →L[ℂ] E)‖ :=
      norm_mul_le _ _
    _ = ‖Polynomial.aeval A p‖ * a := by
      rw [norm_smul, norm_star, norm_one, mul_one]
    _ ≤ (2 * m + a) * a := mul_le_mul_of_nonneg_right hpA ha
    _ ≤ m ^ 2 := hfactor
/-- Universal circle symmetrization applied to `p - C b` controls `p(A)`
after an arbitrary scalar shift.  The symmetrized operator is exactly
`p(A) + (p(c) - 2b)I`, giving the displayed quantitative estimate. -/
theorem
    norm_aeval_le_two_mul_polynomialSupNorm_sub_C_add_norm_eval_sub_two_mul_of_forall_symmetrized_bound
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    {K : Set ℂ}
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K)
    (p : Polynomial ℂ) (b : ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      2 * polynomialSupNorm (p - Polynomial.C b) K +
        ‖Polynomial.eval c p - 2 * b‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · let _ := hE
    have hzero : Polynomial.aeval A p = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    exact add_nonneg
      (mul_nonneg (by norm_num) (polynomialSupNorm_nonneg _ _))
      (norm_nonneg _)
  let _ := hE
  let q : Polynomial ℂ := p - Polynomial.C b
  let r : ℝ := polynomialSupNorm q K
  let d : ℝ := ‖Polynomial.eval c p - 2 * b‖
  have hsym := hsymm q
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
    A c hA q, star_smul, star_one, star_star] at hsym
  have hsymq : ‖Polynomial.aeval A q +
      Polynomial.eval c q • (1 : E →L[ℂ] E)‖ ≤ 2 * r := by
    simpa only [r] using hsym
  have hdecomp : Polynomial.aeval A p =
      (Polynomial.aeval A q +
          Polynomial.eval c q • (1 : E →L[ℂ] E)) -
        (Polynomial.eval c p - 2 * b) • (1 : E →L[ℂ] E) := by
    simp only [q, map_sub, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Polynomial.eval_sub,
      Polynomial.eval_C, sub_smul, two_mul, add_smul]
    abel
  calc
    ‖Polynomial.aeval A p‖ =
        ‖(Polynomial.aeval A q +
            Polynomial.eval c q • (1 : E →L[ℂ] E)) -
          (Polynomial.eval c p - 2 * b) •
            (1 : E →L[ℂ] E)‖ := congrArg norm hdecomp
    _ ≤ ‖Polynomial.aeval A q +
            Polynomial.eval c q • (1 : E →L[ℂ] E)‖ +
          ‖(Polynomial.eval c p - 2 * b) •
            (1 : E →L[ℂ] E)‖ := norm_sub_le _ _
    _ ≤ 2 * r + d := by
      rw [norm_smul, norm_one, mul_one]
      exact add_le_add hsymq (le_refl d)
