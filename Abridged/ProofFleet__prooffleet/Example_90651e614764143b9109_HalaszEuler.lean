import Mathlib
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.LSeries.Dirichlet
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
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v08927546f6f6.MoltResearch.Discrepancy.MultiplicativeC ====
section
/-!
# Discrepancy: ℂ-valued completely multiplicative language layer

First language-layer module for the Tao 2015 analytic core
(`Problems/tao2015_analytic_core.md`): the ℂ-valued predicates the Fourier-reduction and
log-Elliott interfaces are stated over, plus the coercion bridge from the existing ℤ-valued
substrate.

Definitions:
- `CompletelyMultiplicativeC g` — `g (a * b) = g a * g b` for **all** `a b : ℕ` (no coprimality
  hypothesis, mirroring the ℤ-valued `CompletelyMultiplicative`).
- `Unimodular g` — `‖g n‖ = 1` for all `n` (the "valued in the unit circle `S¹`" hypothesis of
  Tao's interfaces, arXiv:1509.05363 §2).

Bridges (the ℤ-valued substrate embeds in the ℂ-valued language):
- `CompletelyMultiplicative.toC` — a ℤ-valued completely multiplicative sequence is completely
  multiplicative after coercion to ℂ.
- `IsSignSequence.unimodularC` — sign sequences are unimodular after coercion to ℂ.

Partial sums:
- `apSumC g d n` — ℂ-valued homogeneous AP partial sum, mirroring `apSum`.
- `CompletelyMultiplicativeC.apSumC_eq_mul_apSumC_one` — the multiplicative collapse
  `apSumC g d n = g d * apSumC g 1 n` (port of `CompletelyMultiplicative.apSum_eq_mul_apSum_one`).
- `CompletelyMultiplicativeC.norm_apSumC_eq_norm_apSumC_one` — its norm-level corollary for
  unimodular `g`: partial-sum growth along any step `d` is the step-one growth.

Design note (from the card's decision record): interfaces for the analytic core must be stated
over ℂ-valued unimodular functions — the ±1 subclass loses the character-modulated cases. The
ℤ-valued bridge below is the hand-off *into* that subclass once a reduction produces candidates,
not a substitute for it.
-/
namespace MoltResearch
/-- A ℂ-valued completely multiplicative sequence: `g (a * b) = g a * g b` for all **nonzero**
`a b : ℕ` (no coprimality hypothesis).

ℂ-valued analogue of `CompletelyMultiplicative`. As there, we do not bake in `g 1 = 1`: it
follows for unimodular sequences (`CompletelyMultiplicativeC.map_one_of_unimodular`), and keeping
the definition minimal makes it easier to produce.

The `a ≠ 0 → b ≠ 0` guards are load-bearing (issue #2879): the literature defines completely
multiplicative functions on `{1, 2, ...}`, and an unguarded law instantiated at `b = 0` gives
`g 0 = g a * g 0` for every `a`, which under any nonvanishing-at-`0` condition (`Unimodular`)
collapses the class to the constant-1 function and vacates every theorem quantifying over it.
With the guards, `g 0` is genuinely unconstrained junk.
-/
def CompletelyMultiplicativeC (g : ℕ → ℂ) : Prop :=
  ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → g (a * b) = g a * g b

namespace Unimodular
variable {g : ℕ → ℂ}

end Unimodular
namespace CompletelyMultiplicativeC
variable {g : ℕ → ℂ}
end CompletelyMultiplicativeC
namespace CompletelyMultiplicative
variable {f : ℕ → ℤ}
end CompletelyMultiplicative
namespace IsSignSequence
variable {f : ℕ → ℤ}
end IsSignSequence
end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v08927546f6f6.MoltResearch.Discrepancy.PretentiousDist ====
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

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_90651e614764143b9109_HalaszEuler ====
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
/-- **The band sup for the smooth polynomial** (Track R, M2-i4c1a):
on any frequency `ξ`, the `y₂`-smooth phase polynomial truncated at
`x` is bounded by the 1-line Euler product bound — the prime mass
minus the pretentious distance floor `M` at scale `x`, corrected by
twice the mass difference (the truncation transfer) — plus the
Rankin-`δ` polynomial-versus-series tail. This is the `Bband` input
of the band/tail Hölder split, with every constant explicit. -/
theorem norm_smooth_poly_band_le (f : ℕ → ℂ)
    (hcm : CompletelyMultiplicativeC f) (h1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) (y₂ x : ℕ) (hy₂ : 1 ≤ y₂) (hyx : y₂ ≤ x)
    (hx : 1 ≤ x) (ξ M δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hM : M ≤ pretentiousDistSq f
      (fun n => (n:ℂ)^(Complex.I*((2*Real.pi*ξ : ℝ):ℂ))) x) 
    (h_MoltResearch_smooth_tsum_eq_finprod : ∀ (f : ℕ → ℂ),
      MoltResearch.CompletelyMultiplicativeC f →
        f 1 = 1 →
          (∀ (n : ℕ), ‖f n‖ ≤ 1) →
            ∀ (y : ℕ),
              1 ≤ y →
                ∀ (s : ℂ),
                  s.re = 1 →
                    (∑' (n : ℕ),
                        (if n ∈ y.smoothNumbers then f n else 0) *
                          if n = 0 then 0 else (↑n : ℂ) ^ (-s)) =
                      ∏ p ∈ y.primesBelow, (1 - f p * (↑p : ℂ) ^ (-s))⁻¹)
    (h_MoltResearch_pretentiousDistSq_le_add_mass : ∀ (g h : ℕ → ℂ),
      (∀ (p : ℕ), ‖g p‖ ≤ 1) →
        (∀ (p : ℕ), ‖h p‖ ≤ 1) →
          ∀ {y x : ℕ},
            y ≤ x →
              MoltResearch.pretentiousDistSq g h x ≤
                MoltResearch.pretentiousDistSq g h y +
                  2 * (∑ p ∈ x.primesBelow, 1 / (↑p : ℝ) - ∑ p ∈ y.primesBelow, 1 / (↑p : ℝ)))
    (h_MoltResearch_norm_smooth_finprod_le : ∀ (f : ℕ → ℂ),
      (∀ (n : ℕ), ‖f n‖ ≤ 1) →
        ∀ (y : ℕ) (ξ : ℝ),
          ‖∏ p ∈ y.primesBelow, (1 - f p * (↑p : ℂ) ^ (-(1 + Complex.I * (↑ξ : ℂ))))⁻¹‖ ≤
            Real.exp
              (∑ p ∈ y.primesBelow, 1 / (↑p : ℝ) -
                  MoltResearch.pretentiousDistSq f (fun (n : ℕ) ↦ (↑n : ℂ) ^ (Complex.I * (↑ξ : ℂ))) y +
                1))
    (h_MoltResearch_norm_smooth_tsum_sub_sum_le : ∀ (f : ℕ → ℂ),
      (∀ (n : ℕ), ‖f n‖ ≤ 1) →
        ∀ (y X : ℕ),
          1 ≤ X →
            ∀ (s : ℂ),
              s.re = 1 →
                ∀ (δ : ℝ),
                  0 < δ →
                    δ < 1 →
                      ‖(∑' (n : ℕ),
                              (if n ∈ y.smoothNumbers then f n else 0) *
                                if n = 0 then 0 else (↑n : ℂ) ^ (-s)) -
                            ∑ n ∈ X.smoothNumbersUpTo y,
                              (if n ∈ y.smoothNumbers then f n else 0) *
                                if n = 0 then 0 else (↑n : ℂ) ^ (-s)‖ ≤
                        (↑X : ℝ) ^ (-δ) * ∏ p ∈ y.primesBelow, (1 - (↑p : ℝ) ^ (δ - 1))⁻¹)
    :
    ‖∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂),
        (f n/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)‖
      ≤ Real.exp ((∑ p ∈ y₂.primesBelow, (1:ℝ)/p) - M
            + 2*((∑ p ∈ x.primesBelow, (1:ℝ)/p)
              - (∑ p ∈ y₂.primesBelow, (1:ℝ)/p)) + 1)
        + (x:ℝ)^(-δ) * ∏ p ∈ y₂.primesBelow, (1 - (p:ℝ)^(δ-1))⁻¹ := by
  classical
  set c : ℝ := 2*Real.pi*ξ with hc_def
  set s : ℂ := 1 + Complex.I*((c:ℝ):ℂ) with hs_def
  have hsre : s.re = 1 := by
    rw [hs_def]
    simp
  -- the polynomial index set is the smooth-numbers-up-to Finset
  have hconv : (Finset.Icc 1 x).filter (· ∈ Nat.smoothNumbers y₂)
      = Nat.smoothNumbersUpTo x y₂ := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      exact ⟨⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers h3),
        h2⟩, h3⟩
  -- each term is the L-series term at s = 1 + 2πiξ
  have hterm : ∀ n ∈ Nat.smoothNumbersUpTo x y₂,
      (f n/(n:ℂ)) * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ)
        = (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
            * (if n = 0 then 0 else (n:ℂ)^(-s)) := by
    intro n hn
    rw [Nat.mem_smoothNumbersUpTo] at hn
    have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hn.2
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [if_pos hn.2, if_neg hn0]
    have hn0' : (n:ℂ) ≠ 0 := by exact_mod_cast hn0
    have hlogn : Complex.log (n:ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [show ((n:ℕ):ℂ) = (((n:ℕ):ℝ):ℂ) from by norm_cast]
      exact (Complex.ofReal_log hnpos.le).symm
    have hcpow : (n:ℂ)^(-s)
        = ((1:ℂ)/(n:ℂ))
          * ((Real.fourierChar (-(Real.log n * ξ)) : Circle) : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero hn0', hlogn,
        Real.fourierChar_apply]
      rw [show ((Real.log n : ℝ) : ℂ) * (-s)
          = ((-(Real.log n) : ℝ) : ℂ)
            + ((2*Real.pi*(-(Real.log n * ξ)) : ℝ) : ℂ) * Complex.I from by
        rw [hs_def, hc_def]
        push_cast
        ring]
      rw [Complex.exp_add]
      congr 1
      rw [← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hnpos]
      rw [one_div]
      push_cast
      ring
    rw [hcpow]
    ring
  rw [hconv, Finset.sum_congr rfl hterm]
  -- triangle against the full smooth series
  set T : ℂ := ∑' n : ℕ, (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
    * (if n = 0 then 0 else (n:ℂ)^(-s)) with hT_def
  set A : ℂ := ∑ n ∈ Nat.smoothNumbersUpTo x y₂,
    (if n ∈ Nat.smoothNumbers y₂ then f n else 0)
      * (if n = 0 then 0 else (n:ℂ)^(-s)) with hA_def
  have htri : ‖A‖ ≤ ‖T‖ + ‖T - A‖ := by
    calc ‖A‖ = ‖T - (T - A)‖ := by
          congr 1
          ring
      _ ≤ ‖T‖ + ‖T - A‖ := norm_sub_le _ _
  refine le_trans htri (add_le_add ?_ ?_)
  · -- the head: Euler product bound + distance transfer
    have heq := h_MoltResearch_smooth_tsum_eq_finprod f hcm h1 hb y₂ hy₂ s hsre
    rw [hT_def, heq]
    have hprod := h_MoltResearch_norm_smooth_finprod_le f hb y₂ c
    have hshape : ∏ p ∈ y₂.primesBelow,
        (1 - (f p) * (p:ℂ)^(-(1 + Complex.I*((c:ℝ):ℂ))))⁻¹
          = ∏ p ∈ y₂.primesBelow, (1 - (f p) * (p:ℂ)^(-s))⁻¹ := by
      rw [hs_def]
    rw [hshape] at hprod
    refine le_trans hprod ?_
    rw [Real.exp_le_exp]
    -- the truncation transfer on the pretentious distance
    have htwist_norm : ∀ p,
        ‖(fun n : ℕ => (n:ℂ)^(Complex.I*((c:ℝ):ℂ))) p‖ ≤ 1 := by
      intro p
      dsimp only
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp
        rcases eq_or_ne (Complex.I*((c:ℝ):ℂ)) 0 with h | h
        · rw [h, Complex.cpow_zero]
          norm_num
        · rw [show ((0:ℕ):ℂ) = 0 from by norm_cast,
            Complex.zero_cpow h]
          norm_num
      · rw [Complex.norm_natCast_cpow_of_pos hp]
        have hre : (Complex.I*((c:ℝ):ℂ)).re = 0 := by
          simp [Complex.mul_re]
        rw [hre, Real.rpow_zero]
    have htrans := h_MoltResearch_pretentiousDistSq_le_add_mass f
      (fun n : ℕ => (n:ℂ)^(Complex.I*((c:ℝ):ℂ)))
      (fun p => hb p) htwist_norm hyx
    have hMc : M ≤ pretentiousDistSq f
        (fun n : ℕ => (n:ℂ)^(Complex.I*((c:ℝ):ℂ))) x := hM
    linarith [htrans, hMc]
  · -- the tail: the Rankin-δ polynomial-versus-series gap
    exact h_MoltResearch_norm_smooth_tsum_sub_sum_le f hb y₂ x hx s hsre δ hδ0 hδ1
end MoltResearch
