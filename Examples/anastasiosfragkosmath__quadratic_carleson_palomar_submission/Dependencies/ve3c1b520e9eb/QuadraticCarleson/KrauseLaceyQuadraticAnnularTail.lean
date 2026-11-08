import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.HardyLittlewoodMaximal
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.HilbertL2Fourier
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.ve3c1b520e9eb.QuadraticCarleson.QuadraticFixedHeightAveragingNorm
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Maximal tails of separated quadratic frequency pieces

This file isolates the frequency-projection part of the direct quadratic
one-node argument.  A finite tail is written as the total sum minus a
prefix.  If every prefix is a smooth low-pass projection of the total sum,
and the low-pass kernels are pointwise dominated by a fixed multiple of the
centered Hardy--Littlewood maximal function, then the whole family of tails
has a cardinality-free `L²` bound.

The application-specific input may be supplied either pointwise through
`HasLowPassPrefixControl` or almost everywhere through
`HasAELowPassPrefixControl`.  The latter is the natural interface for `L²`
Fourier multipliers.  No maximal-tail theorem or orthogonality principle is
assumed here.
-/
open Function MeasureTheory Set FourierTransform Metric
open scoped ENNReal NNReal ComplexConjugate
namespace QuadraticCarleson.KrauseLaceyQuadraticAnnularTail
set_option autoImplicit false
noncomputable section
/-- The pointwise total of a finite sequence of frequency pieces. -/
def finitePieceTotal (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, u j x
/-- The prefix strictly below `n`. -/
def finitePiecePrefix (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, u j x
/-- The finite tail beginning at `n`, represented as total minus prefix.
For `n ≤ N` this is exactly `∑_{n ≤ j < N} u_j`. -/
def finitePieceTail (N : ℕ) (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  finitePieceTotal N u x - finitePiecePrefix u n x
/-- The maximum of the tails beginning at `0, ..., N`. -/
def finitePieceTailMax (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finitePieceTail N u n x‖ₑ
/-- The exact pointwise input supplied by smooth low-pass projections.
The constant is in `ℝ≥0∞` so it composes directly with the project's
maximal-function estimate. -/
def HasLowPassPrefixControl (N : ℕ) (u : ℕ → ℝ → ℂ) (A : ℝ≥0∞) : Prop :=
  ∀ n ≤ N, ∀ x,
    ‖finitePiecePrefix u n x‖ₑ ≤
      A * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x
/-- The measure-theoretically natural version of low-pass prefix control.
Fourier multiplier identities in `L²` determine representatives only almost
everywhere, and this is sufficient for every subsequent `lintegral` estimate. -/
def HasAELowPassPrefixControl (N : ℕ) (u : ℕ → ℝ → ℂ) (A : ℝ≥0∞) : Prop :=
  ∀ n ≤ N, ∀ᵐ x : ℝ ∂volume,
    ‖finitePiecePrefix u n x‖ₑ ≤
      A * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x
/-- Convolution with a kernel supported in a centered rational interval and
bounded by `A / (2r)` is pointwise controlled by `A` times the centered
Hardy--Littlewood maximal function.  This is the basic estimate used for
each smooth low-pass cutoff after decomposing its rapidly decaying kernel
into centered dyadic shells. -/
theorem enorm_convolution_le_maximal_of_supported_kernel
    (q : PositiveRational) {A : ℝ≥0∞} {K f : ℝ → ℂ}
    (hf : Measurable f)
    (hKsupport : Function.support K ⊆ closedBall (0 : ℝ) (q : ℝ))
    (hKnorm : ∀ t, ‖K t‖ₑ ≤ A / ENNReal.ofReal (2 * (q : ℝ)))
    (x : ℝ) :
    ‖∫ y, K (x - y) * f y‖ₑ ≤
      A * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let r : ℝ := q
  let d : ℝ≥0∞ := ENNReal.ofReal (2 * r)
  have hr : 0 < r := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
    simpa only [r] using this
  have hd0 : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint (y : ℝ) :
      ‖K (x - y) * f y‖ₑ ≤
        (closedBall x r).indicator (fun z ↦ (A / d) * ‖f z‖ₑ) y := by
    by_cases hy : y ∈ closedBall x r
    · rw [indicator_of_mem hy, enorm_mul]
      exact mul_le_mul' (by simpa [d, r] using hKnorm (x - y)) le_rfl
    · rw [indicator_of_notMem hy]
      have hzero : K (x - y) = 0 := by
        by_contra hne
        have hb := hKsupport hne
        apply hy
        simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_sub_comm] using hb
      simp [hzero]
  calc
    ‖∫ y, K (x - y) * f y‖ₑ ≤ ∫⁻ y, ‖K (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, (closedBall x r).indicator
        (fun z ↦ (A / d) * ‖f z‖ₑ) y := lintegral_mono hpoint
    _ = (A / d) * ∫⁻ y in closedBall x r, ‖f y‖ₑ := by
      rw [lintegral_indicator measurableSet_closedBall]
      exact lintegral_const_mul'' (A / d)
        (hf.enorm.aemeasurable.restrict)
    _ = A * centeredAverage r (fun y ↦ ‖f y‖ₑ) x := by
      simp only [centeredAverage]
      rw [show ENNReal.ofReal (2 * r) = d from rfl]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ A * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      apply mul_le_mul' le_rfl
      exact le_iSup (fun q' : PositiveRational ↦
        centeredAverage (q' : ℝ) (fun y ↦ ‖f y‖ₑ) x) q
theorem finitePieceTailMax_le_total_add_maximal
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hprefix : HasLowPassPrefixControl N u A) (x : ℝ) :
    finitePieceTailMax N u x ≤
      ‖finitePieceTotal N u x‖ₑ +
        A * centeredHardyLittlewoodMaximal
          (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
  apply Finset.sup_le
  intro n hn
  have hnN : n ≤ N := by
    simpa only [Finset.mem_range] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  exact enorm_sub_le.trans
    (add_le_add le_rfl (hprefix n hnN x))
/-- Almost-everywhere tail domination from almost-everywhere prefix control.
The exceptional sets for the finitely many prefixes are intersected before
taking the finite supremum. -/
theorem finitePieceTailMax_le_total_add_maximal_ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hprefix : HasAELowPassPrefixControl N u A) :
    ∀ᵐ x : ℝ ∂volume,
      finitePieceTailMax N u x ≤
        ‖finitePieceTotal N u x‖ₑ +
          A * centeredHardyLittlewoodMaximal
            (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
  have hall : ∀ᵐ x : ℝ ∂volume,
      ∀ n ∈ Finset.range (N + 1),
        ‖finitePiecePrefix u n x‖ₑ ≤
          A * centeredHardyLittlewoodMaximal
            (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact hprefix n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  filter_upwards [hall] with x hx
  apply Finset.sup_le
  intro n hn
  exact enorm_sub_le.trans (add_le_add le_rfl (hx n hn))
theorem measurable_finitePieceTotal {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j < N, Measurable (u j)) :
    Measurable (finitePieceTotal N u) := by
  classical
  unfold finitePieceTotal
  exact Finset.measurable_sum _ fun j hj ↦ hu j (Finset.mem_range.mp hj)
private theorem ennreal_add_sq_le_four_sum_sq (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hab : a + b ≤ 2 * max a b := by
    calc
      a + b ≤ max a b + max a b :=
        add_le_add (le_max_left a b) (le_max_right a b)
      _ = 2 * max a b := by ring
  have hmax : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    by_cases h : a ≤ b
    · rw [max_eq_right h]
      exact le_add_left le_rfl
    · rw [max_eq_left (le_of_not_ge h)]
      exact le_add_right le_rfl
  calc
    (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' hab 2
    _ = 4 * (max a b) ^ 2 := by ring
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl hmax
/-- Cardinality-free maximal-tail `L²` estimate.  The explicit coefficient
is `4 + 128 A²`, coming from a top-safe ENNReal square estimate and the proved centered
Hardy--Littlewood constant `32`. -/
theorem finitePieceTailMax_sq_lintegral_le
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hu : ∀ j, Measurable (u j))
    (hprefix : HasLowPassPrefixControl N u A) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
      (4 + 128 * A ^ 2) *
        ∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2 := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ‖finitePieceTotal N u x‖ₑ
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal F
  have hF : Measurable F :=
    (measurable_finitePieceTotal fun j _ ↦ hu j).enorm
  have hpoint (x : ℝ) :
      finitePieceTailMax N u x ^ 2 ≤
        4 * (F x ^ 2 + (A * M x) ^ 2) := by
    exact (pow_le_pow_left' (finitePieceTailMax_le_total_add_maximal hprefix x) 2).trans
      (ennreal_add_sq_le_four_sum_sq (F x) (A * M x))
  calc
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
        ∫⁻ x, 4 * (F x ^ 2 + (A * M x) ^ 2) :=
      lintegral_mono hpoint
    _ = 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * ∫⁻ x, M x ^ 2) := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left (hF.pow_const 2)]
      rw [lintegral_const_mul'' (A ^ 2)
        ((measurable_centeredHardyLittlewoodMaximal hF).pow_const 2).aemeasurable]
    _ ≤ 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * (32 * ∫⁻ x, F x ^ 2)) := by
      gcongr
      exact centeredHardyLittlewoodMaximal_sq_lintegral_le hF
    _ = (4 + 128 * A ^ 2) * ∫⁻ x, F x ^ 2 := by ring
/-- Cardinality-free maximal-tail `L²` estimate from almost-everywhere
low-pass prefix control.  This is the form used by Fourier multiplier
applications, whose canonical representatives agree only almost everywhere. -/
theorem finitePieceTailMax_sq_lintegral_le_ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hu : ∀ j, Measurable (u j))
    (hprefix : HasAELowPassPrefixControl N u A) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
      (4 + 128 * A ^ 2) *
        ∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2 := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ‖finitePieceTotal N u x‖ₑ
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal F
  have hF : Measurable F :=
    (measurable_finitePieceTotal fun j _ ↦ hu j).enorm
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      finitePieceTailMax N u x ^ 2 ≤
        4 * (F x ^ 2 + (A * M x) ^ 2) := by
    filter_upwards [finitePieceTailMax_le_total_add_maximal_ae hprefix] with x hx
    exact (pow_le_pow_left' hx 2).trans
      (ennreal_add_sq_le_four_sum_sq (F x) (A * M x))
  calc
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
        ∫⁻ x, 4 * (F x ^ 2 + (A * M x) ^ 2) :=
      lintegral_mono_ae hpoint
    _ = 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * ∫⁻ x, M x ^ 2) := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left (hF.pow_const 2)]
      rw [lintegral_const_mul'' (A ^ 2)
        ((measurable_centeredHardyLittlewoodMaximal hF).pow_const 2).aemeasurable]
    _ ≤ 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * (32 * ∫⁻ x, F x ^ 2)) := by
      gcongr
      exact centeredHardyLittlewoodMaximal_sq_lintegral_le hF
    _ = (4 + 128 * A ^ 2) * ∫⁻ x, F x ^ 2 := by ring
end
end QuadraticCarleson.KrauseLaceyQuadraticAnnularTail
