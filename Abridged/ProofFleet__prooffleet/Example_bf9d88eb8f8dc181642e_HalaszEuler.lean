import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v7d99bdc274d8.MoltResearch.Discrepancy.PretentiousDist ====
section
/-!
# Discrepancy: pretentious (Granville–Soundararajan) distance, finite-`N` form

Language-layer module for the Tao 2015 analytic core (`Problems/tao2015_analytic_core.md`):
the finite-truncation pretentious distance used to state the non-pretentiousness hypothesis of
the logarithmically averaged Elliott theorem (arXiv:1509.05422):

`𝔻(g, h; N)² = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

Conventions:
- The prime range is `Nat.primesBelow N` (primes strictly below `N`) — the Mathlib-idiomatic
  finite prime truncation; interfaces quantifying over all `N` are insensitive to `< N` vs `≤ N`.
- The **squared** distance `pretentiousDistSq` is the primary definition (the literature works
  with `𝔻²` throughout); `pretentiousDist` is its square root.
- Junk values are embraced: without unimodularity hypotheses the summands can be negative, so
  the order lemmas below carry `Unimodular` hypotheses rather than baking them into the
  definition.

Monotonicity basics (this module deliberately stops here):
- `pretentiousDistSq_summand_nonneg`, `pretentiousDistSq_nonneg` — nonnegativity for unimodular
  arguments.
- `pretentiousDistSq_mono` / `pretentiousDist_mono` — monotone in the truncation `N`.
- `Unimodular.pretentiousDistSq_self` — the diagonal vanishes (each summand is `0`).
-/
namespace MoltResearch
/-- Squared finite-`N` pretentious distance (Granville–Soundararajan):

`pretentiousDistSq g h N = ∑_{p prime, p < N} (1 - Re(g p * conj (h p))) / p`.

The non-pretentiousness hypothesis of the log-Elliott interface says this tends to `∞` with `N`
for every character-modulated comparison `h`.
-/
noncomputable def pretentiousDistSq (g h : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, (1 - (g p * (starRingEnd ℂ) (h p)).re) / p
variable {g h : ℕ → ℂ}
namespace Unimodular
end Unimodular
/-! ### Quasi-triangle inequality

The sharp Granville–Soundararajan triangle inequality for `pretentiousDist` is not needed by
the derivation-(C) bookkeeping (all its pretense bounds are `O(1)`), so we state only the
elementary squared-distance version with constant `3`, which has a pointwise proof on the
closed unit disc. -/
end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_bf9d88eb8f8dc181642e_HalaszEuler ====
/-!
# Track C: the Euler-product log bridge, upper direction (Track R, C4b-1)

The pointwise Euler input of the Halász leg: for a completely
multiplicative `f` bounded by `1`, just right of the `1`-line,

  `log ‖L_f(s)‖ ≤ ∑'_p Re(f(p) p^{−s}) + 1`.

This is the mirror of `EulerLogBridge.tsum_re_dirichlet_le_log_norm_LSeries`
(which bounds the prime sum *by* the L-norm), generalized from Dirichlet
characters to arbitrary completely multiplicative bounded `f` via Mathlib's
`EulerProduct.exp_tsum_primes_log_eq_tsum`. Both directions share the same
second-order tail: `∑_p ‖log(1−w_p)⁻¹ − w_p‖ ≤ ∑_p p^{−2} ≤ 1`.

Downstream (C4b-2/3): truncation at `y` and Mertens turn this into
`‖L_f(1 + 1/log y − it)‖ ≤ C · (log y) · exp(−D(f, p^{it}; y)²)` — the
Halász-quality pointwise decay on the non-pretentious range, consumed by
the `𝒯₀`-window bound and the `𝒯₁`-mean-square assembly (C4e).
-/
open Complex
namespace MoltResearch
set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **The 1-line smooth Euler bound** (Track R, M2-i4a2): the finite
Euler product of a `1`-bounded function over the primes below `y`,
evaluated on the 1-line at frequency `ξ`, is exponentially controlled
by the prime mass minus the pretentious distance to the `ξ`-twist —
the `L^∞` input of the cheap-Halász band term, with no abscissa
shift. -/
theorem norm_smooth_finprod_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1)
    (y : ℕ) (ξ : ℝ) 
    (h_MoltResearch_sum_one_div_mul_pred_primesBelow_le : ∀ (y : ℕ), ∑ p ∈ y.primesBelow, 1 / ((↑p : ℝ) * ((↑p : ℝ) - 1)) ≤ 1)
    :
    ‖∏ p ∈ y.primesBelow, (1 - (f p) * (p:ℂ)^(-(1 + Complex.I*(ξ:ℂ))))⁻¹‖
      ≤ Real.exp ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y + 1) := by
  classical
  set s : ℂ := 1 + Complex.I*(ξ:ℂ) with hs_def
  set w : ℕ → ℂ := fun p => f p * (p:ℂ)^(-s) with hw_def
  have hsre : s.re = 1 := by
    rw [hs_def]
    simp
  -- per-prime norm facts
  have hnw : ∀ p ∈ y.primesBelow, ‖w p‖ ≤ 1/(p:ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    have hp0 : 0 < p := hpp.pos
    rw [hw_def]
    dsimp only
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have hre : (-s).re = -1 := by
      rw [Complex.neg_re, hsre]
    rw [hre, Real.rpow_neg_one]
    rw [one_div]
    have h1 : ‖f p‖ * ((p:ℝ))⁻¹ ≤ 1 * ((p:ℝ))⁻¹ := by
      refine mul_le_mul_of_nonneg_right (hb p) ?_
      positivity
    linarith [h1]
  have hhalf : ∀ p ∈ y.primesBelow, ‖w p‖ ≤ 1/2 := by
    intro p hp
    have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
    refine le_trans (hnw p hp) ?_
    rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < p)) (by norm_num)]
    have : (2:ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hlt1 : ∀ p ∈ y.primesBelow, ‖w p‖ < 1 := by
    intro p hp
    have := hhalf p hp
    linarith
  -- per-factor exponential bound
  have hfac : ∀ p ∈ y.primesBelow,
      ‖(1 - w p)⁻¹‖ ≤ Real.exp ((w p).re + ‖w p‖^2) := by
    intro p hp
    have hne : (1 : ℂ) - w p ≠ 0 := by
      intro h
      have h1 : ‖(1:ℂ)‖ = ‖w p‖ := by
        rw [show (1:ℂ) = w p from by linear_combination h]
      rw [norm_one] at h1
      have := hlt1 p hp
      linarith
    have hpos : 0 < ‖(1 - w p)⁻¹‖ := by
      rw [norm_inv]
      have : 0 < ‖(1:ℂ) - w p‖ := norm_pos_iff.mpr hne
      positivity
    rw [← Real.exp_log hpos, Real.exp_le_exp]
    have hlogre : Real.log ‖(1 - w p)⁻¹‖
        = (Complex.log ((1 - w p)⁻¹)).re := by
      rw [Complex.log_re]
    rw [hlogre]
    have hbound := Complex.norm_log_one_sub_inv_sub_self_le (hlt1 p hp)
    have hre_diff : (Complex.log ((1 - w p)⁻¹)).re - (w p).re
        ≤ ‖Complex.log ((1 - w p)⁻¹) - w p‖ := by
      calc (Complex.log ((1 - w p)⁻¹)).re - (w p).re
          = (Complex.log ((1 - w p)⁻¹) - w p).re := by
            rw [Complex.sub_re]
        _ ≤ ‖Complex.log ((1 - w p)⁻¹) - w p‖ := Complex.re_le_norm _
    have hinv2 : (1 - ‖w p‖)⁻¹ ≤ 2 := by
      have := hhalf p hp
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hsq : ‖w p‖^2 * (1 - ‖w p‖)⁻¹ / 2 ≤ ‖w p‖^2 := by
      have h0 : (0:ℝ) ≤ ‖w p‖^2 := sq_nonneg _
      nlinarith
    linarith [hbound, hre_diff, hsq]
  -- assemble the product
  calc ‖∏ p ∈ y.primesBelow, (1 - w p)⁻¹‖
      = ∏ p ∈ y.primesBelow, ‖(1 - w p)⁻¹‖ := norm_prod _ _
    _ ≤ ∏ p ∈ y.primesBelow, Real.exp ((w p).re + ‖w p‖^2) := by
        refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) hfac
    _ = Real.exp (∑ p ∈ y.primesBelow, ((w p).re + ‖w p‖^2)) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp ((∑ p ∈ y.primesBelow, (1:ℝ)/p)
          - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y + 1) := by
        rw [Real.exp_le_exp]
        have hsum_re : ∑ p ∈ y.primesBelow, (w p).re
            = (∑ p ∈ y.primesBelow, (1:ℝ)/p)
              - pretentiousDistSq f (fun n => (n:ℂ)^(Complex.I*(ξ:ℂ))) y := by
          unfold pretentiousDistSq
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hpp := Nat.prime_of_mem_primesBelow hp
          have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
          have hsplit : w p = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ) := by
            rw [hw_def]
            dsimp only
            rw [hs_def]
            rw [show -(1 + Complex.I*(ξ:ℂ))
                = (-(Complex.I*(ξ:ℂ))) + (-1) from by ring]
            rw [Complex.cpow_add _ _ (by
              exact_mod_cast hpp.ne_zero : ((p:ℕ):ℂ) ≠ 0)]
            rw [Complex.cpow_neg_one]
            field_simp
          rw [hsplit]
          have hdiv_re : ((f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ)).re
              = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))).re / (p:ℝ) := by
            have h1 : (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ)))) / (p:ℂ)
                = (f p * (p:ℂ)^(-(Complex.I*(ξ:ℂ))))
                  * (((1/(p:ℝ)):ℝ):ℂ) := by
              push_cast
              field_simp
            rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              mul_zero, sub_zero, mul_one_div]
          rw [hdiv_re]
          have hconjp : (starRingEnd ℂ) (((p:ℕ):ℂ)^(Complex.I*(ξ:ℂ)))
              = ((p:ℕ):ℂ)^(-(Complex.I*(ξ:ℂ))) := by
            have hplus : ((p:ℕ):ℂ) ^ (Complex.I * (ξ:ℂ))
                = Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) := by
              rw [Complex.cpow_def_of_ne_zero
                (by exact_mod_cast hpp.ne_zero)]
              congr 1
              push_cast
              ring
            have hminus : ((p:ℕ):ℂ) ^ (-(Complex.I * (ξ:ℂ)))
                = Complex.exp (-(((ξ * Real.log p : ℝ) : ℂ) * Complex.I)) := by
              rw [Complex.cpow_def_of_ne_zero
                (by exact_mod_cast hpp.ne_zero)]
              congr 1
              push_cast
              ring
            rw [hplus, hminus, ← Complex.exp_conj, map_mul,
              Complex.conj_ofReal, Complex.conj_I]
            ring_nf
          dsimp only
          rw [hconjp]
          ring
        have hsum_sq : ∑ p ∈ y.primesBelow, ‖w p‖^2 ≤ 1 := by
          have h1 : ∑ p ∈ y.primesBelow, ‖w p‖^2
              ≤ ∑ p ∈ y.primesBelow, (1/(p:ℝ))^2 := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hle := hnw p hp
            have h0 : (0:ℝ) ≤ ‖w p‖ := norm_nonneg _
            nlinarith
          have h2 : ∑ p ∈ y.primesBelow, (1/(p:ℝ))^2
              ≤ ∑ p ∈ y.primesBelow, 1/((p:ℝ)*((p:ℝ)-1)) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp2 : (2:ℝ) ≤ p := by
              exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
            rw [div_pow, one_pow]
            rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
            nlinarith
          linarith [h1, h2, h_MoltResearch_sum_one_div_mul_pred_primesBelow_le y]
        rw [Finset.sum_add_distrib, hsum_re]
        linarith [hsum_sq]
end MoltResearch
