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

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_e827f4d0a2387afc0fa2_HalaszMontgomeryLargeValues ====
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


set_option linter.unusedVariables false in
/-- **H-3, well-spaced kernel row.**  The diagonal contributes `N`;
the three off-diagonal pieces are respectively the harmonic gap mass,
the square-root gap mass, and the number of remaining points. -/
theorem sum_norm_halaszKernel_sub_le (N : ℕ) (T : ℝ) (𝒯 : Finset ℝ)
    (t : ℝ) (hT : 1 ≤ T) (ht : t ∈ 𝒯)
    (hrange : ∀ s ∈ 𝒯, |s| ≤ T)
    (hsep : ∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) 
    (h_MoltResearch_sum_inv_abs_sub_erase_le : ∀ (T : ℝ) (𝒯 : Finset ℝ) (t : ℝ),
      1 ≤ T →
        t ∈ 𝒯 →
          (∀ s ∈ 𝒯, |s| ≤ T) →
            (∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) →
              ∑ s ∈ 𝒯.erase t, 1 / |t - s| ≤ 2 * (Real.log (2 * T) + 1))
    (h_MoltResearch_norm_halaszKernel_le : ∀ (N : ℕ) (u : ℝ),
      1 ≤ |u| →
        ‖MoltResearch.halaszKernel N u‖ ≤
          40 * ((↑N : ℝ) / |u| + √|u| * (Real.log (2 * (↑N : ℝ)) + 1) + 1))
    (h_MoltResearch_sum_sqrt_abs_sub_erase_le : ∀ (T : ℝ) (𝒯 : Finset ℝ),
      ∀ t ∈ 𝒯, (∀ s ∈ 𝒯, |s| ≤ T) → ∑ s ∈ 𝒯.erase t, √|t - s| ≤ (↑𝒯.card : ℝ) * √(2 * T))
    (h_MoltResearch_norm_halaszKernel_zero : ∀ (N : ℕ), ‖MoltResearch.halaszKernel N 0‖ = (↑N : ℝ))
    :
    ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      ≤ (N : ℝ) + 80 * (N : ℝ) * (Real.log (2 * T) + 1)
        + 40 * (𝒯.card : ℝ) *
          (Real.sqrt (2 * T) * (Real.log (2 * (N : ℝ)) + 1) + 1) := by
  classical
  let LN := Real.log (2 * (N : ℝ)) + 1
  have hLN0 : 0 ≤ LN := by
    by_cases hN0 : N = 0
    · subst N
      simp [LN]
    · have htwoN : (1 : ℝ) ≤ 2 * (N : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * N by omega)
      have := Real.log_nonneg htwoN
      simp only [LN]
      linarith
  have hdiag : ‖halaszKernel N (t - t)‖ = (N : ℝ) := by
    simpa using h_MoltResearch_norm_halaszKernel_zero N
  have hoff : ∀ s ∈ 𝒯.erase t,
      ‖halaszKernel N (t - s)‖
        ≤ 40 * ((N : ℝ) / |t - s| + Real.sqrt |t - s| * LN + 1) := by
    intro s hs
    have hsT : s ∈ 𝒯 := Finset.mem_of_mem_erase hs
    have hne : t ≠ s := by
      exact ne_comm.mp (Finset.ne_of_mem_erase hs)
    have hgap := hsep t ht s hsT hne
    simpa only [LN] using h_MoltResearch_norm_halaszKernel_le N (t - s) hgap
  have hoffsum : ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖
      ≤ 40 * ((N : ℝ) * (∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|)
        + LN * (∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|)
        + ((𝒯.erase t).card : ℝ)) := by
    refine (Finset.sum_le_sum hoff).trans_eq ?_
    have hA : ∑ s ∈ 𝒯.erase t, (N : ℝ) / |t - s|
        = (N : ℝ) * ∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have hB : ∑ s ∈ 𝒯.erase t, Real.sqrt |t - s| * LN
        = LN * ∑ s ∈ 𝒯.erase t, Real.sqrt |t - s| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    calc
      ∑ s ∈ 𝒯.erase t,
          40 * ((N : ℝ) / |t - s| + Real.sqrt |t - s| * LN + 1)
          = 40 * ∑ s ∈ 𝒯.erase t,
              ((N : ℝ) / |t - s| + Real.sqrt |t - s| * LN + 1) := by
            rw [Finset.mul_sum]
      _ = 40 * ((∑ s ∈ 𝒯.erase t, (N : ℝ) / |t - s|)
            + (∑ s ∈ 𝒯.erase t, Real.sqrt |t - s| * LN)
            + ((𝒯.erase t).card : ℝ)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            mul_one]
      _ = 40 * ((N : ℝ) * (∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|)
            + LN * (∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|)
            + ((𝒯.erase t).card : ℝ)) := by rw [hA, hB]
  have hinv := h_MoltResearch_sum_inv_abs_sub_erase_le T 𝒯 t hT ht hrange hsep
  have hsqrt := h_MoltResearch_sum_sqrt_abs_sub_erase_le T 𝒯 t ht hrange
  have hcardNat : (𝒯.erase t).card ≤ 𝒯.card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  have hcard : ((𝒯.erase t).card : ℝ) ≤ (𝒯.card : ℝ) := by
    exact_mod_cast hcardNat
  have hinvN := mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg N)
  have hsqrtLN := mul_le_mul_of_nonneg_left hsqrt hLN0
  have hofffinal : ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖
      ≤ 80 * (N : ℝ) * (Real.log (2 * T) + 1)
        + 40 * (𝒯.card : ℝ) *
          (Real.sqrt (2 * T) * (Real.log (2 * (N : ℝ)) + 1) + 1) := by
    refine hoffsum.trans ?_
    simp only [LN] at hsqrtLN ⊢
    nlinarith
  have hsplit : ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      = ‖halaszKernel N (t - t)‖
        + ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖ := by
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ ht).symm
  rw [hsplit, hdiag]
  linarith
/-! ## The absolute-constant ledger -/

end MoltResearch
