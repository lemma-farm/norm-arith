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

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_1d63e7eb13f53853d93e_HalaszMontgomeryLargeValues ====
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


set_option linter.unusedVariables false in
/-- Every dyadic block is either in the second-difference range or in
the Kusmin–Landau tail.  This combined form is convenient for summing all
blocks without exposing the case split to callers. -/
theorem norm_sum_e_neg_log_dyadic_block_le (v : ℝ) (M P : ℕ)
    (hv : 1 ≤ v) (hM : 1 ≤ M) (hMP : M ≤ P) (hP : P ≤ 2 * M) 
    (h_MoltResearch_norm_sum_e_neg_log_Ioc_le_kusmin : ∀ (v : ℝ) (M P : ℕ),
      0 < v →
        1 ≤ M →
          M ≤ P →
            P ≤ 2 * M →
              13 * v ≤ 12 * (↑(M + 1) : ℝ) →
                ‖∑ n ∈ Finset.Ioc M P, MoltResearch.ExpSums.e (-(v * Real.log (↑n : ℝ)))‖ ≤
                  12 * (↑(M + 1) : ℝ) / v)
    (h_MoltResearch_ExpSums_norm_sum_e_le_card : ∀ (W : Finset ℕ) (ψ : ℕ → ℝ), ‖∑ n ∈ W, MoltResearch.ExpSums.e (ψ n)‖ ≤ (↑W.card : ℝ))
    (h_MoltResearch_norm_sum_e_neg_log_Ioc_le_vdc : ∀ (v : ℝ) (M P : ℕ),
      0 < v →
        1 ≤ M →
          M ≤ P →
            P ≤ 2 * M →
              v < (↑(M + 1) : ℝ) ^ 2 →
                ‖∑ n ∈ Finset.Ioc M P, MoltResearch.ExpSums.e (-(v * Real.log (↑n : ℝ)))‖ ≤
                  7 * √v + 12 * (↑(M + 1) : ℝ) / √v + 2)
    :
    ‖∑ n ∈ Finset.Ioc M P, ExpSums.e (-(v * Real.log n))‖
      ≤ 22 * Real.sqrt v + 12 * (M + 1 : ℕ) / v := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hs1 : 1 ≤ Real.sqrt v := by
    have := Real.sqrt_le_sqrt hv
    simpa using this
  by_cases hlarge : 13 * v ≤ 12 * (M + 1 : ℕ)
  · have hkl := h_MoltResearch_norm_sum_e_neg_log_Ioc_le_kusmin v M P hv0 hM hMP hP hlarge
    exact hkl.trans (le_add_of_nonneg_left (by positivity))
  · have hsmall : 12 * ((M + 1 : ℕ) : ℝ) < 13 * v := by
      push_neg at hlarge
      exact hlarge
    by_cases hvM : v < (M + 1 : ℕ) ^ 2
    · have hvdc := h_MoltResearch_norm_sum_e_neg_log_Ioc_le_vdc v M P hv0 hM hMP hP hvM
      refine hvdc.trans ?_
      have hss : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0.le
      have hAs : 12 * ((M + 1 : ℕ) : ℝ) / Real.sqrt v
          ≤ 13 * Real.sqrt v := by
        apply (div_le_iff₀ hs).mpr
        rw [mul_assoc, hss]
        exact hsmall.le
      have hbase : 7 * Real.sqrt v
            + 12 * ((M + 1 : ℕ) : ℝ) / Real.sqrt v + 2
          ≤ 22 * Real.sqrt v := by
        nlinarith
      exact hbase.trans (le_add_of_nonneg_right (by positivity))
    · have hvM' : (((M + 1 : ℕ) : ℝ) ^ 2) ≤ v := by
        push_neg at hvM
        exact hvM
      have hA0 : (0 : ℝ) ≤ (M + 1 : ℕ) := by positivity
      have hAs : ((M + 1 : ℕ) : ℝ) ≤ Real.sqrt v :=
        (Real.le_sqrt hA0 hv0.le).mpr hvM'
      have htriv := h_MoltResearch_ExpSums_norm_sum_e_le_card (Finset.Ioc M P)
        (fun n : ℕ => -(v * Real.log n))
      rw [Nat.card_Ioc] at htriv
      have hcardNat : P - M ≤ M := by omega
      have hcard : (((P - M : ℕ) : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hcardNat
      have hMAs : (M : ℝ) ≤ (M + 1 : ℕ) := by push_cast; linarith
      refine htriv.trans ?_
      have : (((P - M : ℕ) : ℝ)) ≤ Real.sqrt v := hcard.trans (hMAs.trans hAs)
      nlinarith [show 0 ≤ 12 * ((M + 1 : ℕ) : ℝ) / v by positivity]

/-! ## Well-spaced kernel rows -/

/-! ## The absolute-constant ledger -/

end MoltResearch
