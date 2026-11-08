import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.LargeValues
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.RepairCompatAliases
/-!
# Track C: the dyadic mean value theorem (Track R, C4d-1)

The `[MR]`-Lemma-14-style mean value theorem for `1`-bounded Dirichlet
polynomials with **integer** (not prime) support on a dyadic range: for
any `S ⊆ [N, 2N]`,

  `∫_{−L}^{L} ‖∑_{n∈S} (a_n/n)·e(−ξ log n)‖² dξ
     ≤ 2L·∑ 1/n² + (log N + 1)·∑ 1/n`

— diagonal plus one harmonic log. Runs on the same oscillation-kernel
toolkit as the C4a window energy (`pair_integral_diag_le`,
`pair_integral_offdiag_le`, which need only `1 ≤ n`); the off-diagonal
gap sums are harmonic (`k ↦ p ± k` reindexed into `[1, N]`) rather than
Brun–Titchmarsh, because integer support is dense.

This is the `∫|Q|²`-leg of the `𝒰`-moment machinery: in the `𝒯₁`
assembly (C4e) the short block-polynomial gets this MVT while the long
factor gets the pointwise Halász ratio bound (`HalaszEuler.lean`).
-/
open Finset
namespace MoltResearch
namespace ExpSums
theorem norm_sq_sum_mul_le_sum_mul_sum (P : Finset ℕ) (w z : ℕ → ℂ) :
    ‖∑ p ∈ P, w p * z p‖^2
      ≤ (∑ p ∈ P, ‖w p‖) * (∑ p ∈ P, ‖w p‖ * ‖z p‖^2) := by
  have h1 : ‖∑ p ∈ P, w p * z p‖ ≤ ∑ p ∈ P, ‖w p‖ * ‖z p‖ := by
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    exact Finset.sum_congr rfl fun p _ => norm_mul _ _
  have h2 : (∑ p ∈ P, ‖w p‖ * ‖z p‖)^2
      ≤ (∑ p ∈ P, ‖w p‖) * (∑ p ∈ P, ‖w p‖ * ‖z p‖^2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
      (fun p => Real.sqrt ‖w p‖) (fun p => Real.sqrt ‖w p‖ * ‖z p‖)
    have hL : ∀ p ∈ P, Real.sqrt ‖w p‖ * (Real.sqrt ‖w p‖ * ‖z p‖)
        = ‖w p‖ * ‖z p‖ := by
      intro p _
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have hf : ∀ p ∈ P, Real.sqrt ‖w p‖ ^ 2 = ‖w p‖ := by
      intro p _
      exact Real.sq_sqrt (norm_nonneg _)
    have hg : ∀ p ∈ P, (Real.sqrt ‖w p‖ * ‖z p‖) ^ 2 = ‖w p‖ * ‖z p‖^2 := by
      intro p _
      rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hf,
      Finset.sum_congr rfl hg] at hcs
    exact hcs
  calc ‖∑ p ∈ P, w p * z p‖^2
      ≤ (∑ p ∈ P, ‖w p‖ * ‖z p‖)^2 := by
        have hnn : (0:ℝ) ≤ ‖∑ p ∈ P, w p * z p‖ := norm_nonneg _
        nlinarith [h1, hnn]
    _ ≤ (∑ p ∈ P, ‖w p‖) * (∑ p ∈ P, ‖w p‖ * ‖z p‖^2) := h2
theorem intervalIntegral_norm_sq_freq_weighted_sum_le (P : Finset ℕ)
    (w : ℕ → ℝ → ℂ) (v : ℕ → ℝ) (hw : ∀ p ξ, ‖w p ξ‖ ≤ v p)
    (hwcont : ∀ p, Continuous (w p))
    (z : ℕ → ℝ → ℂ) (hzcont : ∀ p, Continuous (z p))
    (L : ℝ) (hL : 0 ≤ L) :
    ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p ξ * z p ξ‖^2
      ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ∫ ξ in (-L)..L, ‖z p ξ‖^2 := by
  classical
  have hv0 : ∀ p, 0 ≤ v p := fun p => le_trans (norm_nonneg _) (hw p 0)
  have hcontF : Continuous (fun ξ : ℝ => ‖∑ p ∈ P, w p ξ * z p ξ‖^2) := by
    refine Continuous.pow ?_ 2
    refine Continuous.norm ?_
    exact continuous_finsetSum _ fun p _ => ((hwcont p).mul (hzcont p))
  have hcontR : Continuous (fun ξ : ℝ => ∑ p ∈ P, v p * ‖z p ξ‖^2) :=
    continuous_finsetSum _ fun p _ =>
      continuous_const.mul ((hzcont p).norm.pow 2)
  have hpt : ∀ ξ : ℝ, ‖∑ p ∈ P, w p ξ * z p ξ‖^2
      ≤ (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ‖z p ξ‖^2 := by
    intro ξ
    have hcs := norm_sq_sum_mul_le_sum_mul_sum P (fun p => w p ξ)
      (fun p => z p ξ)
    refine le_trans hcs ?_
    refine mul_le_mul (Finset.sum_le_sum fun p _ => hw p ξ)
      (Finset.sum_le_sum fun p _ => ?_)
      (Finset.sum_nonneg fun p _ => by positivity)
      (Finset.sum_nonneg fun p _ => hv0 p)
    exact mul_le_mul_of_nonneg_right (hw p ξ) (by positivity)
  have hstep1 : ∫ ξ in (-L)..L, ‖∑ p ∈ P, w p ξ * z p ξ‖^2
      ≤ ∫ ξ in (-L)..L, (∑ p ∈ P, v p) * ∑ p ∈ P, v p * ‖z p ξ‖^2 := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
    · exact hcontF.intervalIntegrable _ _
    · exact (continuous_const.mul hcontR).intervalIntegrable _ _
    · intro ξ _
      exact hpt ξ
  refine le_trans hstep1 ?_
  rw [intervalIntegral.integral_const_mul]
  have hsum_nonneg : (0:ℝ) ≤ ∑ p ∈ P, v p :=
    Finset.sum_nonneg fun p _ => hv0 p
  refine mul_le_mul_of_nonneg_left ?_ hsum_nonneg
  rw [intervalIntegral.integral_finset_sum
    (f := fun p ξ => v p * ‖z p ξ‖^2)
    (fun p _ =>
      (continuous_const.mul ((hzcont p).norm.pow 2)).intervalIntegrable _ _)]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [intervalIntegral.integral_const_mul]
open MeasureTheory Real in
/-- **The Gaussian majorant** (Track R, M0-f): `e^{π}e^{−πt²} ≥ 1`
exactly on `[−1,1]`.  This is the majorant of GHS Lemma 2.6 — they use
a Fejér-type `Φ` with compactly supported transform, but only rapid
decay of `𝓕Φ` is actually needed, and the Gaussian is its own
transform (`fourierIntegral_gaussian_pi`), which Mathlib supplies. -/
theorem one_le_gaussian_majorant {t : ℝ} (ht : |t| ≤ 1) :
    1 ≤ Real.exp π * Real.exp (-(π*t^2)) := by
  rw [← Real.exp_add]
  refine Real.one_le_exp ?_
  have h1 : t^2 ≤ 1 := by
    have := abs_le.mp ht
    nlinarith [this.1, this.2]
  nlinarith [Real.pi_pos]
open MeasureTheory Real in
/-- **The majorant step of GHS Lemma 2.6** (Track R, M0-f): a sharp
interval integral is dominated by the Gaussian-weighted integral over
the whole line.  The weight is `≥ 1` on `[−T,T]` and the integrand is
non-negative, so no cancellation is lost; on the frequency side the
Gaussian's own transform then localises the off-diagonal. -/
theorem intervalIntegral_norm_sq_le_gaussian (D : ℝ → ℂ) (hD : Continuous D)
    (C : ℝ) (hC : ∀ t, ‖D t‖ ≤ C) (T : ℝ) (hT : 0 < T) :
    ∫ t in (-T)..T, ‖D t‖^2
      ≤ ∫ t, ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2))) := by
  have hC0 : (0:ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- the Gaussian weight is integrable
  have hgauss : Integrable (fun t : ℝ => Real.exp (-(π/T^2) * t^2)) := by
    refine integrable_exp_neg_mul_sq ?_
    positivity
  have hweight : ∀ t : ℝ, Real.exp (-(π*(t/T)^2)) = Real.exp (-(π/T^2) * t^2) := by
    intro t
    congr 1
    field_simp
  have hmajint : Integrable
      (fun t : ℝ => ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2)))) := by
    refine Integrable.mono' ((hgauss.const_mul (C^2 * Real.exp π))) ?_ ?_
    · exact ((hD.norm.pow 2).mul
        (continuous_const.mul (by fun_prop))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hweight t]
      have hsq : ‖D t‖^2 ≤ C^2 := by
        have := hC t
        nlinarith [norm_nonneg (D t)]
      calc ‖D t‖^2 * (Real.exp π * Real.exp (-(π/T^2) * t^2))
          ≤ C^2 * (Real.exp π * Real.exp (-(π/T^2) * t^2)) := by
            refine mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = C^2 * Real.exp π * Real.exp (-(π/T^2) * t^2) := by ring
  -- on the interval the weight is at least one
  have hstep : ∀ t ∈ Set.uIcc (-T) T, ‖D t‖^2
      ≤ ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2))) := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have habs : |t/T| ≤ 1 := by
      rw [abs_div, abs_of_pos hT, div_le_one hT]
      rcases abs_le.mp (abs_le.mpr ⟨ht.1, ht.2⟩) with ⟨h1, h2⟩
      exact abs_le.mpr ⟨h1, h2⟩
    have h1 := one_le_gaussian_majorant habs
    nlinarith [sq_nonneg ‖D t‖, norm_nonneg (D t)]
  have hle1 : ∫ t in (-T)..T, ‖D t‖^2
      ≤ ∫ t in (-T)..T, ‖D t‖^2 * (Real.exp π * Real.exp (-(π*(t/T)^2))) := by
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
    · exact ((hD.norm.pow 2)).intervalIntegrable _ _
    · exact hmajint.intervalIntegrable
    · intro t ht
      exact hstep t (by rw [Set.uIcc_of_le (by linarith)]; exact ht)
  refine le_trans hle1 ?_
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_le_integral hmajint ?_
  refine Filter.Eventually.of_forall fun t => ?_
  positivity
open MeasureTheory Real Complex in
open scoped FourierTransform in
/-- **The scaled Gaussian transform** (Track R, M0-g): the Fourier
transform of the width-`T` Gaussian is the width-`1/T` Gaussian, with
the explicit factor `T`.  This is the frequency side of the majorant
`e^{π}e^{−π(t/T)²}` of `intervalIntegral_norm_sq_le_gaussian`: the
transform decays like `e^{−πT²ξ²}`, which is what localises the
off-diagonal of the mean value theorem to `|log(n/m)| ≲ 1/T`. -/
theorem fourier_gaussian_scaled {T : ℝ} (hT : 0 < T) :
    (𝓕 fun x : ℝ => ((Real.exp (-(π*(x/T)^2)) : ℝ) : ℂ))
      = fun ξ : ℝ => ((T : ℝ) : ℂ) * ((Real.exp (-(π*T^2*ξ^2)) : ℝ) : ℂ) := by
  have hTne : (T:ℝ) ≠ 0 := ne_of_gt hT
  set b : ℂ := ((1/T^2 : ℝ) : ℂ) with hb_def
  have hbre : 0 < b.re := by
    rw [hb_def, Complex.ofReal_re]
    positivity
  have hfun : (fun x : ℝ => ((Real.exp (-(π*(x/T)^2)) : ℝ) : ℂ))
      = fun x : ℝ => Complex.exp (-π * b * (x:ℂ)^2) := by
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    rw [hb_def]
    push_cast
    field_simp
  have hbhalf : b^(1/2 : ℂ) = ((1/T : ℝ) : ℂ) := by
    have h1 : ((1/T^2 : ℝ)) ^ ((1/2 : ℝ)) = (1/T : ℝ) := by
      rw [show (1/T^2 : ℝ) = (1/T)^2 from by field_simp]
      rw [← Real.rpow_natCast (1/T) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    calc b^(1/2 : ℂ) = ((1/T^2 : ℝ) : ℂ)^((((1/2 : ℝ)) : ℝ) : ℂ) := by
          rw [hb_def]
          congr 1
          push_cast
          ring
      _ = (((1/T^2 : ℝ) ^ ((1/2 : ℝ)) : ℝ) : ℂ) :=
          (Complex.ofReal_cpow (by positivity) _).symm
      _ = ((1/T : ℝ) : ℂ) := by rw [h1]
  rw [hfun, fourier_gaussian_pi hbre]
  funext ξ
  rw [hbhalf]
  have h2 : (1:ℂ)/((1/T : ℝ) : ℂ) = ((T:ℝ):ℂ) := by
    push_cast
    field_simp
  rw [h2]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  rw [hb_def]
  push_cast
  field_simp
open MeasureTheory in
/-- **The weighted double-sum expansion** (Track R, M0-i): the
weighted mean square of a Dirichlet polynomial is the double sum of
its pair correlations against the weight.  This is the step of GHS
Lemma 2.6 that turns the Gaussian-majorised integral into an
arithmetic double sum; evaluating each pair integral as `𝓕W` at
`log m − log n` is the next step, and the Gaussian's transform is what
then localises the off-diagonal. -/
theorem integral_norm_sq_poly_weight_eq (S : Finset ℕ) (c : ℕ → ℂ)
    (W : ℝ → ℝ) (hWc : Continuous W) (hWi : Integrable W) :
    ∫ ξ, ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 * W ξ
      = ∑ m ∈ S, ∑ n ∈ S, ∫ ξ, (((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re) * W ξ := by
  classical
  -- the pointwise expansion, as in the dyadic mean value theorem
  have hexpand : ∀ ξ : ℝ,
      ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      = ∑ m ∈ S, ∑ n ∈ S, ((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re := by
    intro ξ
    rw [norm_sq_eq_mul_conj_re, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    rw [map_mul, mul_mul_mul_comm]
    congr 1
    exact char_mul_conj_char (Real.log m) (Real.log n) ξ
  -- each pair term is integrable against the weight
  have hterm : ∀ m n : ℕ, Integrable (fun ξ : ℝ =>
      (((c m * (starRingEnd ℂ) (c n))
        * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
          : ℂ)).re) * W ξ) := by
    intro m n
    refine ((hWi.abs).const_mul (‖c m‖ * ‖c n‖)).mono' ?_ ?_
    · refine (Complex.continuous_re.comp ?_).mul hWc |>.aestronglyMeasurable
      refine continuous_const.mul ?_
      exact continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (by fun_prop))
    · refine Filter.Eventually.of_forall fun ξ => ?_
      set z : ℂ := (c m * (starRingEnd ℂ) (c n))
        * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle) : ℂ)
        with hz_def
      have h1 : |z.re| ≤ ‖c m‖ * ‖c n‖ := by
        refine le_trans (Complex.abs_re_le_norm _) ?_
        rw [hz_def, norm_mul, norm_mul, Circle.norm_coe, mul_one,
          RCLike.norm_conj]
      rw [Real.norm_eq_abs, abs_mul]
      calc |z.re| * |W ξ| ≤ (‖c m‖ * ‖c n‖) * |W ξ| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = ‖c m‖ * ‖c n‖ * |W ξ| := by ring
  -- expand, then exchange the finite sums with the integral
  have hpt : ∀ ξ : ℝ, ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2 * W ξ
      = ∑ m ∈ S, ∑ n ∈ S, (((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re) * W ξ := by
    intro ξ
    rw [hexpand ξ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finset_sum _ (fun m _ =>
    MeasureTheory.integrable_finset_sum _ (fun n _ => hterm m n))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MeasureTheory.integral_finset_sum _ (fun n _ => hterm m n)]
open MeasureTheory in
/-- **The pair integral is a transform value** (Track R, M0-j): each
pair term of the weighted double-sum expansion is the real part of the
coefficient product against `𝓕W` at the log-difference.  With the
Gaussian weight of `intervalIntegral_norm_sq_le_gaussian` this is
where the localisation enters: `𝓕W` at `log m − log n` decays like
`e^{−πT²(log m − log n)²}`, so only `|n − m| ≪ m/T` survives. -/
theorem integral_re_char_mul_weight (z : ℂ) (v : ℝ) (W : ℝ → ℝ)
    (hWc : Continuous W) (hWi : Integrable W) :
    ∫ ξ, ((z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re) * W ξ
      = (z * ∫ ξ, ((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re := by
  classical
  have hchar : Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (by fun_prop))
  -- the complex integrand is integrable: the character has modulus one
  have hint : Integrable fun ξ : ℝ => ((W ξ : ℝ) : ℂ)
      * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := by
    refine ((hWi.abs).const_mul 1).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp hWc).mul hchar).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ξ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
        mul_one, one_mul]
  have hintz : Integrable fun ξ : ℝ => z * (((W ξ : ℝ) : ℂ)
      * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)) := hint.const_mul z
  -- the integrands agree pointwise, then `re` exchanges with the integral
  have hpt : ∀ ξ : ℝ,
      ((z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re) * W ξ
      = (z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))).re := by
    intro ξ
    rw [show z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
        = (z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
          * ((W ξ : ℝ) : ℂ) from by ring]
    conv_rhs => rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  calc ∫ ξ, ((z * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re) * W ξ
      = ∫ ξ, (z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))).re :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ ξ, z * (((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))).re :=
        integral_re hintz
    _ = (z * ∫ ξ, ((W ξ : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)).re := by
        rw [MeasureTheory.integral_const_mul]
/-- **The symmetric pair bound** (Track R, M0-k): against a
non-negative symmetric kernel, the double sum of pair correlations
collapses to a diagonal sum.  This is the `2|a(m)a(n)| ≤ |a(m)|² +
|a(n)|²` step of GHS Lemma 2.6: the cross terms are traded for squares
and the symmetry of the kernel folds the two halves together, leaving
one factor free for the Brun–Titchmarsh count. -/
theorem sum_pair_re_le_of_symm (S : Finset ℕ) (c : ℕ → ℂ) (K : ℕ → ℕ → ℝ)
    (hK0 : ∀ m n, 0 ≤ K m n) (hKsymm : ∀ m n, K m n = K n m) :
    ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)).re * K m n
      ≤ ∑ m ∈ S, ‖c m‖^2 * ∑ n ∈ S, K m n := by
  classical
  -- the cross term is at most the average of the squares
  have hstep : ∀ m n : ℕ, (c m * (starRingEnd ℂ) (c n)).re * K m n
      ≤ ((‖c m‖^2 + ‖c n‖^2)/2) * K m n := by
    intro m n
    refine mul_le_mul_of_nonneg_right ?_ (hK0 m n)
    have h1 : (c m * (starRingEnd ℂ) (c n)).re ≤ ‖c m‖ * ‖c n‖ := by
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖c m‖ - ‖c n‖), h1]
  refine le_trans (Finset.sum_le_sum fun m _ =>
    Finset.sum_le_sum fun n _ => hstep m n) ?_
  -- split the average into the two halves
  have hsplit : ∑ m ∈ S, ∑ n ∈ S, ((‖c m‖^2 + ‖c n‖^2)/2) * K m n
      = (∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n)
        + ∑ m ∈ S, ∑ n ∈ S, (‖c n‖^2/2) * K m n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  -- the second half is the first, after exchanging the indices
  have hswap : ∑ m ∈ S, ∑ n ∈ S, (‖c n‖^2/2) * K m n
      = ∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hKsymm n m]
  rw [hsplit, hswap]
  have hcollect : (∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n)
      + ∑ m ∈ S, ∑ n ∈ S, (‖c m‖^2/2) * K m n
      = ∑ m ∈ S, ‖c m‖^2 * ∑ n ∈ S, K m n := by
    rw [← two_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hcollect]
open MeasureTheory Real Complex in
open scoped FourierTransform in
/-- **The Gaussian pair bound** (Track R, M0-v): the sharp window
energy of a Dirichlet polynomial is dominated by the double sum of its
pair correlations against the Gaussian kernel
`e^{π}·T·e^{−πT²(log m − log n)²}`.  This is the whole outer chain of
GHS Lemma 2.6 in one step — majorise by the Gaussian
(`intervalIntegral_norm_sq_le_gaussian`), expand into pairs
(`integral_norm_sq_poly_weight_eq`), evaluate each pair integral as a
transform value (`integral_re_char_mul_weight`), and read that value
off the Gaussian's self-duality (`fourier_gaussian_scaled`).  What
remains is arithmetic: the kernel is symmetric and non-negative, so
`sum_pair_re_le_of_symm` folds it onto the diagonal and `inner_sum_le`
counts the surviving primes. -/
theorem intervalIntegral_norm_sq_gaussian_pairs_le (S : Finset ℕ) (c : ℕ → ℂ)
    (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, c n
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)).re
          * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
  classical
  -- the Gaussian weight is continuous and integrable
  have hWc : Continuous
      (fun ξ : ℝ => Real.exp π * Real.exp (-(π*(ξ/T)^2))) := by fun_prop
  have hweight : ∀ ξ : ℝ,
      Real.exp (-(π*(ξ/T)^2)) = Real.exp (-(π/T^2) * ξ^2) := by
    intro ξ
    congr 1
    field_simp
  have hWi : Integrable
      (fun ξ : ℝ => Real.exp π * Real.exp (-(π*(ξ/T)^2))) := by
    have hfun : (fun ξ : ℝ => Real.exp π * Real.exp (-(π*(ξ/T)^2)))
        = fun ξ : ℝ => Real.exp π * Real.exp (-(π/T^2) * ξ^2) := by
      funext ξ
      rw [hweight ξ]
    rw [hfun]
    exact (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  -- the polynomial is continuous and bounded, so the majorant applies
  have hchar : ∀ v : ℝ, Continuous fun ξ : ℝ =>
      ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ) := fun v =>
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hDc : Continuous fun ξ : ℝ => ∑ n ∈ S, c n
      * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (hchar (Real.log n))
  have hDbound : ∀ ξ : ℝ, ‖∑ n ∈ S, c n
      * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
        ≤ ∑ n ∈ S, ‖c n‖ := by
    intro ξ
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, Circle.norm_coe, mul_one]
  -- the transform of the weight, at the log-difference
  have hFourier : ∀ v : ℝ,
      (∫ ξ : ℝ, ((Real.exp π * Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
        = ((Real.exp π * T * Real.exp (-(π*T^2*v^2)) : ℝ) : ℂ) := by
    intro v
    have hg : (𝓕 fun x : ℝ => ((Real.exp (-(π*(x/T)^2)) : ℝ) : ℂ)) v
        = ((T : ℝ) : ℂ) * ((Real.exp (-(π*T^2*v^2)) : ℝ) : ℂ) :=
      congrFun (fourier_gaussian_scaled hT) v
    simp only [fourier_real_eq] at hg
    have hcomm : (∫ ξ : ℝ, ((Real.exp π * Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ)
          * ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ))
        = ((Real.exp π : ℝ) : ℂ) * ∫ ξ : ℝ,
            (Real.fourierChar (-(ξ * v)) : Circle)
              • ((Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ξ => ?_)
      simp only [Circle.smul_def, smul_eq_mul]
      rw [mul_comm ξ v, Complex.ofReal_mul]
      ring
    rw [hcomm, hg, Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  calc (∫ ξ in (-T)..T, ‖∑ n ∈ S, c n
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∫ ξ : ℝ, ‖∑ n ∈ S, c n
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
            * (Real.exp π * Real.exp (-(π*(ξ/T)^2))) :=
        intervalIntegral_norm_sq_le_gaussian _ hDc _ hDbound T hT
    _ = ∑ m ∈ S, ∑ n ∈ S, ∫ ξ : ℝ, (((c m * (starRingEnd ℂ) (c n))
          * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
            : ℂ)).re) * (Real.exp π * Real.exp (-(π*(ξ/T)^2))) :=
        integral_norm_sq_poly_weight_eq S c _ hWc hWi
    _ = ∑ m ∈ S, ∑ n ∈ S, ((c m * (starRingEnd ℂ) (c n))
          * ((Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)) : ℝ) : ℂ)).re := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
        have h1 : (∫ ξ : ℝ, (((c m * (starRingEnd ℂ) (c n))
                * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ)) : Circle)
                  : ℂ)).re) * (Real.exp π * Real.exp (-(π*(ξ/T)^2))))
              = ((c m * (starRingEnd ℂ) (c n)) * ∫ ξ : ℝ,
                  ((Real.exp π * Real.exp (-(π*(ξ/T)^2)) : ℝ) : ℂ)
                    * ((Real.fourierChar (-((Real.log m - Real.log n) * ξ))
                        : Circle) : ℂ)).re :=
          integral_re_char_mul_weight _ _ _ hWc hWi
        rw [h1, hFourier]
    _ = ∑ m ∈ S, ∑ n ∈ S, (c m * (starRingEnd ℂ) (c n)).re
          * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
open MeasureTheory Real Complex in
/-- **The Gaussian diagonal bound** (Track R, M0-w): for a Dirichlet
polynomial whose coefficients carry a **non-negative real weight** `r`,
the window energy collapses onto the diagonal with `r` moved into the
kernel:

  `∫_{−T}^{T}‖∑ a(n)r(n)n^{−iξ}‖² ≤ ∑ₘ |a(m)|²r(m)·∑ₙ r(n)K(m,n)`.

Carrying `r` in the kernel rather than in the coefficients is the whole
point.  Applying `sum_pair_re_le_of_symm` directly to `c = a·r` would
produce `|a(m)|²r(m)²` on the diagonal — with `r = Λ` that is one
logarithm worse than GHS Lemma 2.6 allows.  Splitting the pair as
`a(m)·conj a(n)` against the weighted kernel `r(m)r(n)K(m,n)` leaves
exactly one `r(m)` outside, which is the `Λ(n)` of `∑ n|a(n)|²Λ(n)`. -/
theorem intervalIntegral_norm_sq_gaussian_diag_le (S : Finset ℕ) (a : ℕ → ℂ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((r n : ℝ) : ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∑ m ∈ S, ‖a m‖^2 * r m
          * ∑ n ∈ S, r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
  classical
  -- the weighted kernel is non-negative and symmetric
  have hK0 : ∀ m n : ℕ, 0 ≤ r m * r n
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
    intro m n
    refine mul_nonneg (mul_nonneg (hr m) (hr n)) ?_
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hT.le) (Real.exp_pos _).le
  have hKsymm : ∀ m n : ℕ, r m * r n
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))
      = r n * r m
      * (Real.exp π * T
          * Real.exp (-(π*T^2*(Real.log n - Real.log m)^2))) := by
    intro m n
    have hsq : (Real.log m - Real.log n)^2 = (Real.log n - Real.log m)^2 := by
      ring
    rw [hsq]
    ring
  -- the weight is real, so it passes through the real part
  have hpair : ∀ m n : ℕ,
      ((a m * ((r m : ℝ) : ℂ)) * (starRingEnd ℂ) (a n * ((r n : ℝ) : ℂ))).re
          * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))
        = (a m * (starRingEnd ℂ) (a n)).re
          * (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) := by
    intro m n
    have hz : (a m * ((r m : ℝ) : ℂ))
          * (starRingEnd ℂ) (a n * ((r n : ℝ) : ℂ))
        = (a m * (starRingEnd ℂ) (a n)) * (((r m * r n : ℝ)) : ℂ) := by
      rw [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
    rw [hz, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  calc (∫ ξ in (-T)..T, ‖∑ n ∈ S, (a n * ((r n : ℝ) : ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ ∑ m ∈ S, ∑ n ∈ S, ((a m * ((r m : ℝ) : ℂ))
          * (starRingEnd ℂ) (a n * ((r n : ℝ) : ℂ))).re
            * (Real.exp π * T
                * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) :=
        intervalIntegral_norm_sq_gaussian_pairs_le S _ T hT
    _ = ∑ m ∈ S, ∑ n ∈ S, (a m * (starRingEnd ℂ) (a n)).re
          * (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) :=
        Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun n _ => hpair m n
    _ ≤ ∑ m ∈ S, ‖a m‖^2
          * ∑ n ∈ S, (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) :=
        sum_pair_re_le_of_symm S a
          (fun m n => r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2)))) hK0 hKsymm
    _ = ∑ m ∈ S, ‖a m‖^2 * r m
          * ∑ n ∈ S, r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        have hfac : ∑ n ∈ S, (r m * r n * (Real.exp π * T
              * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))))
            = r m * ∑ n ∈ S, r n * (Real.exp π * T
                * Real.exp (-(π*T^2*(Real.log m - Real.log n)^2))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
        rw [hfac, ← mul_assoc]
open MeasureTheory in
/-- **The Gaussian tail sum against the integral** (Track R, A2-III,
I-1a): for `c > 0`, `∑_{k=1}^{M} e^{−ck²} ≤ √(π/c)` — the shifted
sum-versus-integral comparison against the Gaussian integral.  This is
the step that makes the short-block mean value theorem log-free; the
constant is deliberately loose (the sharp value is half this). -/
theorem sum_exp_neg_mul_sq_le (c : ℝ) (hc : 0 < c) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, Real.exp (-(c*(k:ℝ)^2))
      ≤ Real.sqrt (Real.pi/c) := by
  classical
  set f : ℝ → ℝ := fun u => Real.exp (-(c*u^2)) with hf_def
  have hanti : AntitoneOn f (Set.Icc (0:ℝ) (0 + (M:ℝ))) := by
    intro u hu v hv huv
    simp only [hf_def]
    refine Real.exp_le_exp.2 ?_
    have hu0 : (0:ℝ) ≤ u := hu.1
    have hsq : u^2 ≤ v^2 := pow_le_pow_left₀ hu0 huv 2
    have := mul_le_mul_of_nonneg_left hsq hc.le
    linarith
  have hcmp := AntitoneOn.sum_le_integral (x₀ := (0:ℝ)) (a := M)
    (f := f) hanti
  have hshift : ∑ k ∈ Finset.Icc 1 M, Real.exp (-(c*(k:ℝ)^2))
      = ∑ i ∈ Finset.range M, f (0 + ((i:ℕ) + 1 : ℕ)) := by
    rw [show Finset.Icc 1 M = (Finset.range M).image (fun i => i + 1) by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨k - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega]
    rw [Finset.sum_image (by intro a _ b _ hab; simpa using hab)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf_def]
    push_cast
    ring_nf
  rw [hshift]
  refine le_trans hcmp ?_
  have hint : Integrable f := by
    simp only [hf_def]
    simpa using integrable_exp_neg_mul_sq hc
  have hnonneg : ∀ u : ℝ, 0 ≤ f u := fun u => (Real.exp_pos _).le
  have hgauss : ∫ u, f u = Real.sqrt (Real.pi/c) := by
    simp only [hf_def]
    simpa using integral_gaussian c
  rw [← hgauss, zero_add, intervalIntegral.integral_of_le (by positivity)]
  refine le_trans (setIntegral_le_integral hint
    (Filter.Eventually.of_forall hnonneg)) ?_
  exact le_rfl
/-- **The block theta sum** (Track R, A2-III, I-1b): for a block
`S ⊆ (A, 2A]` and `m ∈ S`, the Gaussian kernel summed over the block
is at most `1 + 4A/T` — the diagonal term plus two one-sided tails,
each priced by `sum_exp_neg_mul_sq_le` after the log-separation
`|log m − log n| ≥ |m − n|/(2A)`.  This is what makes the short-block
mean value theorem log-free. -/
theorem sum_exp_neg_sq_log_diff_le (A : ℕ) (hA : 1 ≤ A) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ioc A (2*A)) (m : ℕ) (hm : m ∈ S)
    (T : ℝ) (hT : 0 < T) :
    ∑ n ∈ S, Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))
      ≤ 1 + 4*(A:ℝ)/T := by
  classical
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  set c : ℝ := Real.pi*T^2/(4*(A:ℝ)^2) with hc_def
  have hc0 : 0 < c := by
    rw [hc_def]
    positivity
  -- the tail bound, in the shape both halves need
  have htail : Real.sqrt (Real.pi/c) = 2*(A:ℝ)/T := by
    rw [hc_def]
    rw [show Real.pi/(Real.pi*T^2/(4*(A:ℝ)^2)) = (2*(A:ℝ)/T)^2 by
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.Icc 1 M, Real.exp (-(c*(k:ℝ)^2))
      ≤ 2*(A:ℝ)/T := by
    intro M
    rw [← htail]
    exact sum_exp_neg_mul_sq_le c hc0 M
  -- the per-term comparison
  have hterm : ∀ n ∈ S, n ≠ m →
      Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))
        ≤ Real.exp (-(c*(((if n < m then m - n else n - m) : ℕ):ℝ)^2)) := by
    intro n hn hne
    have hnIoc := Finset.mem_Ioc.mp (hS hn)
    have hmIoc := Finset.mem_Ioc.mp (hS hm)
    refine Real.exp_le_exp.2 ?_
    have hkey : ((((if n < m then m - n else n - m) : ℕ)):ℝ)^2/(4*(A:ℝ)^2)
        ≤ (Real.log m - Real.log n)^2 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_pos hlt]
        have hn1 : 1 ≤ n := by omega
        have hsep := log_sub_log_ge n m hn1 hlt
        have hmc : (0:ℝ) < m := by
          have : (0:ℕ) < m := by omega
          exact_mod_cast this
        have hcast : (((m - n : ℕ)):ℝ) = (m:ℝ) - n := by
          have : n ≤ m := hlt.le
          push_cast [Nat.cast_sub this]
          ring
        have hm2A : (m:ℝ) ≤ 2*(A:ℝ) := by exact_mod_cast hmIoc.2
        have hstep : (((m - n : ℕ)):ℝ)/(2*(A:ℝ))
            ≤ Real.log m - Real.log n := by
          rw [hcast]
          refine le_trans ?_ hsep
          rw [div_le_div_iff₀ (by positivity) hmc]
          nlinarith [hmc, hm2A, (by exact_mod_cast hlt.le : (n:ℝ) ≤ m)]
        have hpos : (0:ℝ) ≤ (((m - n : ℕ)):ℝ)/(2*(A:ℝ)) := by positivity
        have hsq := pow_le_pow_left₀ hpos hstep 2
        calc ((((m - n : ℕ))):ℝ)^2/(4*(A:ℝ)^2)
            = ((((m - n : ℕ)):ℝ)/(2*(A:ℝ)))^2 := by
              rw [div_pow]
              ring_nf
          _ ≤ (Real.log m - Real.log n)^2 := hsq
      · rw [if_neg (by omega)]
        have hm1 : 1 ≤ m := by omega
        have hsep := log_sub_log_ge m n hm1 hgt
        have hnc : (0:ℝ) < n := by
          have : (0:ℕ) < n := by omega
          exact_mod_cast this
        have hcast : (((n - m : ℕ)):ℝ) = (n:ℝ) - m := by
          have : m ≤ n := hgt.le
          push_cast [Nat.cast_sub this]
          ring
        have hn2A : (n:ℝ) ≤ 2*(A:ℝ) := by exact_mod_cast hnIoc.2
        have hstep : (((n - m : ℕ)):ℝ)/(2*(A:ℝ))
            ≤ Real.log n - Real.log m := by
          rw [hcast]
          refine le_trans ?_ hsep
          rw [div_le_div_iff₀ (by positivity) hnc]
          nlinarith [hnc, hn2A, (by exact_mod_cast hgt.le : (m:ℝ) ≤ n)]
        have hpos : (0:ℝ) ≤ (((n - m : ℕ)):ℝ)/(2*(A:ℝ)) := by positivity
        have hsq := pow_le_pow_left₀ hpos hstep 2
        have hflip : (Real.log m - Real.log n)^2
            = (Real.log n - Real.log m)^2 := by ring
        rw [hflip]
        calc ((((n - m : ℕ))):ℝ)^2/(4*(A:ℝ)^2)
            = ((((n - m : ℕ)):ℝ)/(2*(A:ℝ)))^2 := by
              rw [div_pow]
              ring_nf
          _ ≤ (Real.log n - Real.log m)^2 := hsq
    rw [hc_def]
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hexp : Real.pi*T^2/(4*(A:ℝ)^2)
          * ((((if n < m then m - n else n - m) : ℕ)):ℝ)^2
        ≤ Real.pi*T^2*(Real.log m - Real.log n)^2 := by
      have := mul_le_mul_of_nonneg_left hkey
        (by positivity : (0:ℝ) ≤ Real.pi*T^2)
      calc Real.pi*T^2/(4*(A:ℝ)^2)
            * ((((if n < m then m - n else n - m) : ℕ)):ℝ)^2
          = Real.pi*T^2
              * (((((if n < m then m - n else n - m) : ℕ)):ℝ)^2/(4*(A:ℝ)^2)) := by
            ring
        _ ≤ Real.pi*T^2*(Real.log m - Real.log n)^2 := this
    linarith
  -- split the block at `m`
  have hsplit : S = (S.filter (fun n => n < m)) ∪ (S.filter (fun n => ¬ n < m)) :=
    (Finset.filter_union_filter_not_eq _ _).symm
  have hlow : ∑ n ∈ S.filter (fun n => n < m),
      Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))
      ≤ 2*(A:ℝ)/T := by
    have hmap : ∀ n ∈ S.filter (fun n => n < m),
        Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))
          ≤ Real.exp (-(c*(((m - n : ℕ)):ℝ)^2)) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have := hterm n hn.1 (by omega)
      rwa [if_pos hn.2] at this
    refine le_trans (Finset.sum_le_sum hmap) ?_
    have hinj : Set.InjOn (fun n => m - n) ↑(S.filter (fun n => n < m)) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      simp only at hab
      omega
    have himg : ∑ n ∈ S.filter (fun n => n < m),
        Real.exp (-(c*(((m - n : ℕ)):ℝ)^2))
        = ∑ k ∈ (S.filter (fun n => n < m)).image (fun n => m - n),
            Real.exp (-(c*(k:ℝ)^2)) :=
      (Finset.sum_image (f := fun k : ℕ => Real.exp (-(c*(k:ℝ)^2))) hinj).symm
    rw [himg]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun k _ _ => (Real.exp_pos _).le)) (hgeom A)
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    rw [Finset.mem_filter] at hn
    have hnIoc := Finset.mem_Ioc.mp (hS hn.1)
    have hmIoc := Finset.mem_Ioc.mp (hS hm)
    rw [Finset.mem_Icc]
    omega
  have hhigh : ∑ n ∈ S.filter (fun n => ¬ n < m),
      Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))
      ≤ 1 + 2*(A:ℝ)/T := by
    have hmem : m ∈ S.filter (fun n => ¬ n < m) := by
      rw [Finset.mem_filter]
      exact ⟨hm, by omega⟩
    rw [← Finset.add_sum_erase _ _ hmem]
    have hdiag : Real.exp (-(Real.pi*T^2*(Real.log m - Real.log m)^2)) = 1 := by
      simp
    rw [hdiag]
    have hgoal : ∀ x y : ℝ, x ≤ y → (1:ℝ) + x ≤ 1 + y := fun x y h => by linarith
    refine hgoal _ _ ?_
    have hmap : ∀ n ∈ (S.filter (fun n => ¬ n < m)).erase m,
        Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))
          ≤ Real.exp (-(c*(((n - m : ℕ)):ℝ)^2)) := by
      intro n hn
      rw [Finset.mem_erase, Finset.mem_filter] at hn
      have := hterm n hn.2.1 hn.1
      rwa [if_neg (by omega)] at this
    refine le_trans (Finset.sum_le_sum hmap) ?_
    have hinj : Set.InjOn (fun n => n - m)
        ↑((S.filter (fun n => ¬ n < m)).erase m) := by
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter] at ha hb
      simp only at hab
      omega
    have himg : ∑ n ∈ (S.filter (fun n => ¬ n < m)).erase m,
        Real.exp (-(c*(((n - m : ℕ)):ℝ)^2))
        = ∑ k ∈ ((S.filter (fun n => ¬ n < m)).erase m).image (fun n => n - m),
            Real.exp (-(c*(k:ℝ)^2)) :=
      (Finset.sum_image (f := fun k : ℕ => Real.exp (-(c*(k:ℝ)^2))) hinj).symm
    rw [himg]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun k _ _ => (Real.exp_pos _).le)) (hgeom A)
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨n, hn, rfl⟩ := hk
    rw [Finset.mem_erase, Finset.mem_filter] at hn
    have hnIoc := Finset.mem_Ioc.mp (hS hn.2.1)
    have hmIoc := Finset.mem_Ioc.mp (hS hm)
    rw [Finset.mem_Icc]
    omega
  have hdisj : Disjoint (S.filter (fun n => n < m))
      (S.filter (fun n => ¬ n < m)) := Finset.disjoint_filter_filter_not _ _ _
  calc ∑ n ∈ S, Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))
      = ∑ n ∈ (S.filter (fun n => n < m)) ∪ (S.filter (fun n => ¬ n < m)),
          Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)) := by
        rw [← hsplit]
    _ = (∑ n ∈ S.filter (fun n => n < m),
            Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)))
          + ∑ n ∈ S.filter (fun n => ¬ n < m),
            Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)) :=
        Finset.sum_union hdisj
    _ ≤ 2*(A:ℝ)/T + (1 + 2*(A:ℝ)/T) := add_le_add hlow hhigh
    _ = 1 + 4*(A:ℝ)/T := by ring
open MeasureTheory in
/-- **The sharp short-block mean value theorem** (Track R, A2-III,
I-2): for a block `S ⊆ (A, 2A]`,

  `∫_{−T}^{T} ‖∑ (c n/n)·e(−ξ log n)‖² ≤ e^π·(T/A + 4)·∑ ‖c n‖²/n`,

the Montgomery–Vaughan large sieve shape for the frequencies `log n`
— **with no logarithm**.  Compare `intervalIntegral_norm_sq_short_poly_le`,
which pays `(log Δ + 1)·∑ 1/n` on the off-diagonal: that logarithm is
an artefact of the pair-by-pair kernel bound, not of the arithmetic.
The Gaussian kit carries the sharp kernel; `sum_exp_neg_sq_log_diff_le`
prices it. -/
theorem intervalIntegral_norm_sq_short_poly_le_sharp (A : ℕ) (hA : 1 ≤ A)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc A (2*A))
    (c : ℕ → ℂ) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (c n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp Real.pi * (T/(A:ℝ) + 4) * ∑ n ∈ S, ‖c n‖^2/(n:ℝ) := by
  classical
  have hA0 : (0:ℝ) < A := by exact_mod_cast hA
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    have := Finset.mem_Ioc.mp (hS hn)
    omega
  -- put the polynomial in the kit's `a · r` shape
  have hshape : ∀ ξ : ℝ, (∑ n ∈ S, (c n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ))
      = ∑ n ∈ S, (c n * (((1/(n:ℝ) : ℝ)) : ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) := by
    intro ξ
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hpos n hn).ne'
    congr 1
    push_cast
    field_simp
  have hbase := intervalIntegral_norm_sq_gaussian_diag_le S c
    (fun n => 1/(n:ℝ)) (fun n => by positivity) T hT
  rw [intervalIntegral.integral_congr (fun ξ _ => by
    rw [hshape ξ] : ∀ ξ ∈ Set.uIcc (-T) T,
      ‖∑ n ∈ S, (c n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2
      = ‖∑ n ∈ S, (c n * (((1/(n:ℝ) : ℝ)) : ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)]
  refine le_trans hbase ?_
  -- price the inner kernel sum by the block theta bound
  have hinner : ∀ m ∈ S, ∑ n ∈ S, (1/(n:ℝ))
        * (Real.exp Real.pi * T
            * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)))
      ≤ (1/(A:ℝ)) * (Real.exp Real.pi * T) * (1 + 4*(A:ℝ)/T) := by
    intro m hm
    have hstep : ∀ n ∈ S, (1/(n:ℝ))
          * (Real.exp Real.pi * T
              * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)))
        ≤ (1/(A:ℝ)) * (Real.exp Real.pi * T)
            * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)) := by
      intro n hn
      have hnA : (A:ℝ) ≤ (n:ℝ) := by
        have := Finset.mem_Ioc.mp (hS hn)
        exact_mod_cast this.1.le
      have hn0 : (0:ℝ) < n := by exact_mod_cast hpos n hn
      have hrecip : (1/(n:ℝ)) ≤ 1/(A:ℝ) := by
        rw [div_le_div_iff₀ hn0 hA0]
        linarith
      have hK0 : (0:ℝ) ≤ Real.exp Real.pi * T
          * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)) := by
        positivity
      calc (1/(n:ℝ)) * (Real.exp Real.pi * T
              * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)))
          ≤ (1/(A:ℝ)) * (Real.exp Real.pi * T
              * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2))) :=
            mul_le_mul_of_nonneg_right hrecip hK0
        _ = (1/(A:ℝ)) * (Real.exp Real.pi * T)
              * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)) := by
            ring
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left
      (sum_exp_neg_sq_log_diff_le A hA S hS m hm T hT) (by positivity)
  -- assemble
  have hcollapse : ∑ m ∈ S, ‖c m‖^2 * (1/(m:ℝ))
        * ∑ n ∈ S, (1/(n:ℝ))
            * (Real.exp Real.pi * T
                * Real.exp (-(Real.pi*T^2*(Real.log m - Real.log n)^2)))
      ≤ ∑ m ∈ S, ‖c m‖^2 * (1/(m:ℝ))
          * ((1/(A:ℝ)) * (Real.exp Real.pi * T) * (1 + 4*(A:ℝ)/T)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    refine mul_le_mul_of_nonneg_left (hinner m hm) ?_
    have hm0 : (0:ℝ) < m := by exact_mod_cast hpos m hm
    positivity
  refine le_trans hcollapse ?_
  rw [← Finset.sum_mul]
  have hfac : (1/(A:ℝ)) * (Real.exp Real.pi * T) * (1 + 4*(A:ℝ)/T)
      = Real.exp Real.pi * (T/(A:ℝ) + 4) := by
    field_simp
  rw [hfac]
  have hmass : ∑ m ∈ S, ‖c m‖^2 * (1/(m:ℝ)) = ∑ n ∈ S, ‖c n‖^2/(n:ℝ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hmass, mul_comm]
open MeasureTheory in
/-- **The sharp short-block mean value theorem, weighted** (Track R,
A2-III, I-3): the `‖c n‖²`-form of
`intervalIntegral_norm_sq_short_poly_le_sharp` relaxed to a uniform
coefficient bound, which the estimate pays for by `B²` — the shape the
band units consume, still with no logarithm. -/
theorem intervalIntegral_norm_sq_short_poly_le_sharp_of_bound (A : ℕ)
    (hA : 1 ≤ A) (S : Finset ℕ) (hS : S ⊆ Finset.Ioc A (2*A))
    (c : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hc : ∀ n, ‖c n‖ ≤ B)
    (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ S, (c n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp Real.pi * (T/(A:ℝ) + 4) * (B^2 * ∑ n ∈ S, (1:ℝ)/(n:ℝ)) := by
  classical
  refine le_trans (intervalIntegral_norm_sq_short_poly_le_sharp A hA S hS
    c T hT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : (0:ℝ) < n := by
    have := Finset.mem_Ioc.mp (hS hn)
    have h1 : 0 < n := by omega
    exact_mod_cast h1
  have hsq : ‖c n‖^2 ≤ B^2 := by
    have := hc n
    nlinarith [norm_nonneg (c n)]
  rw [div_le_iff₀ hn0]
  calc ‖c n‖^2 = ‖c n‖^2 := rfl
    _ ≤ B^2 := hsq
    _ = B^2 * (1/(n:ℝ)) * (n:ℝ) := by field_simp
/-! ## The e-adic telescoping: a window differs from a block by two collars
(Track R, A2-III, II-2a) -/
/-- **The difference of two windows is two edge pieces** (Track R,
A2-III, II-2a): as `Finset`s, with no hypotheses at all,

  `Ioc a b \ Ioc a' b' = Ioc a (min b a') ∪ Ioc (max a b') b`.

Whichever endpoint pair happens to be inverted, the corresponding piece
is empty, so the identity needs no ordering assumption.  This is the
combinatorial core of the `[MR]` decomposition: replacing a
`p`-dependent fibre window by a cell-uniform reference block costs
exactly the two edge pieces, one at each end. -/
theorem Ioc_sdiff_Ioc_eq_union (a b a' b' : ℕ) :
    Finset.Ioc a b \ Finset.Ioc a' b'
      = Finset.Ioc a (min b a') ∪ Finset.Ioc (max a b') b := by
  ext n
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_Ioc]
  omega
/-- The two edge pieces of `Ioc_sdiff_Ioc_eq_union` are disjoint as soon
as the *removed* window is nondegenerate: a point of the left piece is
`≤ a'` and a point of the right piece is `> b'`. -/
theorem disjoint_Ioc_min_Ioc_max {a b a' b' : ℕ} (h : a' ≤ b') :
    Disjoint (Finset.Ioc a (min b a')) (Finset.Ioc (max a b') b) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [Finset.mem_Ioc] at hn hn'
  omega
/-- Splitting a sum against a second `Finset`: `∑_s = ∑_t + ∑_{s∖t} −
∑_{t∖s}`.  Pure bookkeeping, in any additive group. -/
theorem sum_eq_sum_add_sum_sdiff_sub_sum_sdiff {ι M : Type*} [DecidableEq ι]
    [AddCommGroup M] (s t : Finset ι) (f : ι → M) :
    ∑ n ∈ s, f n = ∑ n ∈ t, f n + ∑ n ∈ s \ t, f n - ∑ n ∈ t \ s, f n := by
  have h1 := Finset.sum_inter_add_sum_sdiff s t f
  have h2 := Finset.sum_inter_add_sum_sdiff t s f
  rw [Finset.inter_comm] at h2
  rw [← h1, ← h2]
  abel
/-- **The e-adic telescoping identity** (Track R, A2-III, II-2a): a sum
over the window `(a, b]` equals the same sum over any reference window
`(a', b']` plus four *explicit* collars, two at each end —

  `∑_{(a,b]} f = ∑_{(a',b']} f + (∑_{(a, min b a']} f + ∑_{(max a b', b]} f)
                             − (∑_{(a', min b' a]} f + ∑_{(max a' b, b']} f)`.

This is an **identity**, not an estimate: nothing is lost, and the four
collars are `Ioc`s of endpoints built from `a, b, a', b'` alone — in
particular they do not depend on `f`, so a consumer may keep them under
an integral sign.  That is what the `[MR]` band assembly needs: on an
e-adic cell of primes the fibre window `(A/p, (A+Δ)/p]` varies with `p`,
and this lemma trades it for the cell's fixed reference block, at the
price of collars that `collar_energy_le` then prices at `1/N` each.

Exactly one collar in each pair is nonempty for a given configuration;
stating both keeps the lemma free of case hypotheses beyond the two
windows being nondegenerate. -/
theorem sum_Ioc_eq_sum_Ioc_add_collars {M : Type*} [AddCommGroup M]
    (a b a' b' : ℕ) (hab : a ≤ b) (ha'b' : a' ≤ b') (f : ℕ → M) :
    ∑ n ∈ Finset.Ioc a b, f n
      = ∑ n ∈ Finset.Ioc a' b', f n
        + (∑ n ∈ Finset.Ioc a (min b a'), f n
            + ∑ n ∈ Finset.Ioc (max a b') b, f n)
        - (∑ n ∈ Finset.Ioc a' (min b' a), f n
            + ∑ n ∈ Finset.Ioc (max a' b) b', f n) := by
  classical
  have hkey := sum_eq_sum_add_sum_sdiff_sub_sum_sdiff
    (Finset.Ioc a b) (Finset.Ioc a' b') f
  rw [Ioc_sdiff_Ioc_eq_union, Ioc_sdiff_Ioc_eq_union,
    Finset.sum_union (disjoint_Ioc_min_Ioc_max ha'b'),
    Finset.sum_union (disjoint_Ioc_min_Ioc_max hab)] at hkey
  exact hkey
open MeasureTheory in
/-- **The `L²` triangle inequality, at cost `2`** (Track R, A2-III,
II-2c-0): for continuous `F, G`,

  `∫_{−T}^{T} ‖F + G‖² ≤ 2∫_{−T}^{T} ‖F‖² + 2∫_{−T}^{T} ‖G‖²`.

The `[MR]` telescoping produces a difference of two collar polynomials
anchored at *different* scales, so their energies cannot be merged into
one mean value theorem application; splitting the square is the honest
price, and the factor `2` is absorbed by the `1/N` the collars carry. -/
theorem intervalIntegral_norm_add_sq_le (F G : ℝ → ℂ) (hF : Continuous F)
    (hG : Continuous G) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ξ in (-T)..T, ‖F ξ + G ξ‖^2)
      ≤ 2 * (∫ ξ in (-T)..T, ‖F ξ‖^2)
        + 2 * (∫ ξ in (-T)..T, ‖G ξ‖^2) := by
  have hTT : -T ≤ T := by linarith
  have hFi : IntervalIntegrable (fun ξ => ‖F ξ‖^2) volume (-T) T :=
    (hF.norm.pow 2).intervalIntegrable _ _
  have hGi : IntervalIntegrable (fun ξ => ‖G ξ‖^2) volume (-T) T :=
    (hG.norm.pow 2).intervalIntegrable _ _
  have hsum : IntervalIntegrable (fun ξ => ‖F ξ + G ξ‖^2) volume (-T) T :=
    (((hF.add hG).norm).pow 2).intervalIntegrable _ _
  have hbig : IntervalIntegrable
      (fun ξ => 2 * ‖F ξ‖^2 + 2 * ‖G ξ‖^2) volume (-T) T :=
    (hFi.const_mul 2).add (hGi.const_mul 2)
  have hptwise : ∀ ξ : ℝ, ‖F ξ + G ξ‖^2 ≤ 2 * ‖F ξ‖^2 + 2 * ‖G ξ‖^2 := by
    intro ξ
    have htri : ‖F ξ + G ξ‖ ≤ ‖F ξ‖ + ‖G ξ‖ := norm_add_le _ _
    nlinarith [norm_nonneg (F ξ + G ξ), norm_nonneg (F ξ), norm_nonneg (G ξ),
      sq_nonneg (‖F ξ‖ - ‖G ξ‖)]
  calc (∫ ξ in (-T)..T, ‖F ξ + G ξ‖^2)
      ≤ ∫ ξ in (-T)..T, (2 * ‖F ξ‖^2 + 2 * ‖G ξ‖^2) :=
        intervalIntegral.integral_mono_on hTT hsum hbig (fun ξ _ => hptwise ξ)
    _ = 2 * (∫ ξ in (-T)..T, ‖F ξ‖^2) + 2 * (∫ ξ in (-T)..T, ‖G ξ‖^2) := by
        rw [intervalIntegral.integral_add (hFi.const_mul 2) (hGi.const_mul 2),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
open MeasureTheory in
/-- **The collar energy at an explicit collar length** (Track R, A2-III,
II-2b-0): for a collar `C ⊆ (M, M + L]` no longer than its anchor,

  `∫_{−T}^{T} ‖∑_{n∈C} (d n/n)·e(−ξ log n)‖² ≤ e^π·(T/M + 4)·(L/M)`.

This is the form the `[MR]` telescoping actually produces.  The
collar's length comes out of *natural-number* division bookkeeping —
`|A/p − A/q|` for two primes of one e-adic cell — and is therefore an
explicit `ℕ`, not a clean `M/N`; carrying `L` and paying `L/M` avoids
having to absorb a floor into the resolution parameter.
`collar_energy_le` is the `L = M/N` case. -/
theorem collar_energy_length_le (M L : ℕ) (hM : 1 ≤ M) (hLM : L ≤ M)
    (C : Finset ℕ) (hC : C ⊆ Finset.Ioc M (M + L))
    (d : ℕ → ℂ) (hd : ∀ n, ‖d n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ ξ in (-T)..T, ‖∑ n ∈ C, (d n/(n:ℂ))
        * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖^2)
      ≤ Real.exp Real.pi * (T/(M:ℝ) + 4) * ((L:ℝ)/(M:ℝ)) := by
  classical
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  -- the collar sits in a dyadic range
  have hC2M : C ⊆ Finset.Ioc M (2*M) := by
    refine hC.trans (Finset.Ioc_subset_Ioc_right ?_)
    omega
  have hbase := intervalIntegral_norm_sq_short_poly_le_sharp_of_bound
    M hM C hC2M d 1 (by norm_num) hd T hT
  refine le_trans hbase ?_
  -- the collar's harmonic mass is `L/M`-small: `L` terms, each `≤ 1/M`
  have hmass : ∑ n ∈ C, (1:ℝ)/(n:ℝ) ≤ (L:ℝ)/(M:ℝ) := by
    have hterm : ∀ n ∈ C, (1:ℝ)/(n:ℝ) ≤ 1/(M:ℝ) := by
      intro n hn
      have hnM : M < n := (Finset.mem_Ioc.mp (hC hn)).1
      have hn0 : (0:ℝ) < n := by
        have : (0:ℕ) < n := by omega
        exact_mod_cast this
      have hMn : (M:ℝ) ≤ (n:ℝ) := by exact_mod_cast hnM.le
      rw [div_le_div_iff₀ hn0 hM0]
      linarith
    have hcard : (C.card : ℝ) ≤ (L:ℝ) := by
      have h1 : C.card ≤ L := by
        have hcc := Finset.card_le_card hC
        rwa [Nat.card_Ioc, Nat.add_sub_cancel_left] at hcc
      exact_mod_cast h1
    calc ∑ n ∈ C, (1:ℝ)/(n:ℝ)
        ≤ ∑ _n ∈ C, 1/(M:ℝ) := Finset.sum_le_sum hterm
      _ = (C.card : ℝ) * (1/(M:ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L:ℝ) * (1/(M:ℝ)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (L:ℝ)/(M:ℝ) := by
          ring
  have hconst : (0:ℝ) ≤ Real.exp Real.pi * (T/(M:ℝ) + 4) := by positivity
  calc Real.exp Real.pi * (T/(M:ℝ) + 4) * (1^2 * ∑ n ∈ C, (1:ℝ)/(n:ℝ))
      = Real.exp Real.pi * (T/(M:ℝ) + 4) * (∑ n ∈ C, (1:ℝ)/(n:ℝ)) := by
        ring
    _ ≤ Real.exp Real.pi * (T/(M:ℝ) + 4) * ((L:ℝ)/(M:ℝ)) :=
        mul_le_mul_of_nonneg_left hmass hconst
end ExpSums
end MoltResearch
