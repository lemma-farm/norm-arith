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
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DiophantineApproximation.Basic

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v4ef9114fdbff.MoltResearch.Discrepancy.ExpSums ====
section
/-!
# Discrete exponential sums, layer 1: the Kusmin–Landau inequality (Track L of #3020)

The additive character `e(x) = exp(2πix)`, the nearest-integer distance
`nint`, and the first cancellation estimate for discrete exponential sums:

* `four_nint_le_norm_e_sub_one` — the geometric floor `4·‖x‖ ≤ ‖e(x) − 1‖`
  (Euler split `e(x) − 1 = e(x/2)·2i·sin(πx)` + Jordan's inequality);
* `inv_e_sub_one_eq` — the increment inverses live on a vertical line:
  `(e(δ) − 1)⁻¹ = −1/2 − (i/2)·cot(πδ)` on `(0,1)`;
* `cotpi_sub_cotpi` — the cotangent difference is a sine quotient
  (`cot(πa) − cot(πb) = sin(π(b−a))/(sin(πa)sin(πb))`), giving antitonicity
  with no calculus;
* `sum_diff_mul_eq` — the Abel rearrangement for difference-weighted sums;
* `kusmin_landau` — **the Kusmin–Landau inequality** with explicit constant
  `1`: if the phase increments `φ(n+1) − φ(n)` are monotone and confined to
  `[θ, 1−θ]`, then `‖∑_{M ≤ n ≤ N} e(φ(n))‖ ≤ 1/θ`, uniformly in the length.

Layer 2 (same campaign): the **discrete van der Corput second-derivative
test** `vdc2` — convex phases with second differences `≥ r` and total
increment variation `≤ D` satisfy
`‖∑ e(φ(n))‖ ≤ (D + 2)·(2θ/r + 1/θ + 1)` for every separation `θ`. The
proof is calculus-free: `sum_level_le` charges each unit of increment
growth one short bad prefix (the `delta_climb` through an integer's
`θ`-neighborhood) plus one Kusmin–Landau block (`kusmin_landau_shift` —
the character cannot see the integer part of the slope, `e_intCast`), and
`vdc2_aux` runs the level-budget recursion.

Layer 3 (same campaign): **Weyl differencing** (`weyl_differencing`, the
van der Corput A-process) — `‖∑ e(φ(n))‖² ≤ ((L+H)/H)·(L + 2∑_{g<H} ‖T_g‖)`
with `T_g` the difference-phase sums `∑ e(φ(m+g) − φ(m))`: the `H`-fold
shifted-window average, discrete Cauchy–Schwarz, the conjugate-pair
expansion, and the three-way diagonal/upper/lower split with the
off-diagonal fibering (each difference `g` occurs at most `H` times).
-/
namespace MoltResearch
namespace ExpSums
open Complex
/-- The normalized additive character `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * x * Complex.I)

end ExpSums
end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_7cf0454d7e22eac11b8a_HalaszMontgomeryLargeValues ====
/-!
# Halász–Montgomery large values

This leaf develops the elementary Hilbert-space and exponential-sum argument
behind Iwaniec–Kowalski, Theorem 9.6.  The first unit is the finite-dimensional
duality step: the squared norm of a synthesis operator is controlled by the
largest absolute row sum of its Gram kernel.
-/
namespace MoltResearch
open Finset

/-! ## The logarithmic Dirichlet kernel -/
/-- The unweighted logarithmic Dirichlet kernel used in the
Halász–Montgomery Gram matrix. -/
noncomputable def halaszKernel (N : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ExpSums.e (-(u * Real.log n))

/-! ## Well-spaced kernel rows -/

/-! ## The absolute-constant ledger -/


set_option linter.unusedVariables false in
/-- **Halász–Montgomery large values.**  This is the theorem form of
Iwaniec–Kowalski, Theorem 9.6, with the normalization and explicit
constant used by `HalaszLargeValuesAssumption.bound`. -/
theorem halaszMontgomery_large_values 
    (h_MoltResearch_sum_norm_halaszKernel_sub_le_sixty_four : ∀ (N : ℕ) (T : ℝ) (𝒯 : Finset ℝ) (t : ℝ),
      1 ≤ T →
        t ∈ 𝒯 →
          (∀ s ∈ 𝒯, |s| ≤ T) →
            (∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) →
              ∑ s ∈ 𝒯, ‖MoltResearch.halaszKernel N (t - s)‖ ≤
                64 * ((↑N : ℝ) + (↑𝒯.card : ℝ) * √T) * (Real.log (2 * T) + 1))
    (h_MoltResearch_sum_norm_sq_le_norm_sq_mul_sup_kernel : ∀ {ι κ : Type} (I : Finset ι) (J : Finset κ) (b : ι → ℂ) (χ : ι → κ → ℂ) (B : ℝ),
      0 ≤ B →
        (∀ t ∈ J, ∑ s ∈ J, ‖∑ i ∈ I, χ i t * (starRingEnd ℂ : ℂ → ℂ) (χ i s)‖ ≤ B) →
          ∑ t ∈ J, ‖∑ i ∈ I, b i * χ i t‖ ^ 2 ≤ (∑ i ∈ I, ‖b i‖ ^ 2) * B)
    (h_MoltResearch_ExpSums_e_mul_conj : ∀ (x y : ℝ),
      MoltResearch.ExpSums.e x * (starRingEnd ℂ : ℂ → ℂ) (MoltResearch.ExpSums.e y) =
        MoltResearch.ExpSums.e (x - y))
    :
    ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (𝒯 : Finset ℝ),
      1 ≤ T → (∀ t ∈ 𝒯, |t| ≤ T) →
      (∀ t ∈ 𝒯, ∀ u ∈ 𝒯, t ≠ u → 1 ≤ |t - u|) →
      ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2
        ≤ 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
            * (Real.log (2 * T) + 1)
            * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  classical
  intro N a T 𝒯 hT hrange hsep
  let B := 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
    * (Real.log (2 * T) + 1)
  have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ B := by
    simp only [B]
    positivity
  have hchar : ∀ x : ℝ,
      ((Real.fourierChar x : Circle) : ℂ) = ExpSums.e x := by
    intro x
    rw [Real.fourierChar_apply, ExpSums.e]
    congr 1
    push_cast
    ring
  have hrow : ∀ t ∈ 𝒯,
      ∑ s ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N,
        ExpSums.e (-(Real.log n * t))
          * (starRingEnd ℂ) (ExpSums.e (-(Real.log n * s)))‖ ≤ B := by
    intro t ht
    have hkernel : ∀ s ∈ 𝒯,
        (∑ n ∈ Finset.Icc 1 N,
          ExpSums.e (-(Real.log n * t))
            * (starRingEnd ℂ) (ExpSums.e (-(Real.log n * s))))
          = halaszKernel N (t - s) := by
      intro s _hs
      rw [halaszKernel]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [h_MoltResearch_ExpSums_e_mul_conj]
      congr 1
      ring
    calc
      ∑ s ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N,
          ExpSums.e (-(Real.log n * t))
            * (starRingEnd ℂ) (ExpSums.e (-(Real.log n * s)))‖
          = ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖ := by
              exact Finset.sum_congr rfl fun s hs => by rw [hkernel s hs]
      _ ≤ B := by
        simpa only [B] using
          h_MoltResearch_sum_norm_halaszKernel_sub_le_sixty_four N T 𝒯 t hT ht hrange hsep
  have hdual := h_MoltResearch_sum_norm_sq_le_norm_sq_mul_sup_kernel
    (Finset.Icc 1 N) 𝒯 (fun n => a n / (n : ℂ))
    (fun n t => ExpSums.e (-(Real.log n * t))) B hB0 hrow
  have hlhs :
      (∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
        * ((Real.fourierChar (-(Real.log n * t)) : Circle) : ℂ)‖ ^ 2)
        = ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N, (a n / (n : ℂ))
          * ExpSums.e (-(Real.log n * t))‖ ^ 2 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hchar]
  have hmass : ∑ n ∈ Finset.Icc 1 N, ‖a n / (n : ℂ)‖ ^ 2
      = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [norm_div, Complex.norm_natCast]
    ring
  rw [hlhs]
  calc
    ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 N,
        (a n / (n : ℂ)) * ExpSums.e (-(Real.log n * t))‖ ^ 2
        ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n / (n : ℂ)‖ ^ 2) * B := hdual
    _ = 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
          * (Real.log (2 * T) + 1)
          * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      rw [hmass]
      simp only [B]
      ring
end MoltResearch
