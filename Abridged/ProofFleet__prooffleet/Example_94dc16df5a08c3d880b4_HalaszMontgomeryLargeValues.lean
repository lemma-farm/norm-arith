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

-- ==== Examples.ProofFleet__prooffleet.Dependencies.v41ed75aad5f4.MoltResearch.Discrepancy.ExpSums ====
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

/-- The character has unit modulus. -/
axiom norm_e (x : ℝ) : ‖e x‖ = 1

end ExpSums
end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_94dc16df5a08c3d880b4_HalaszMontgomeryLargeValues ====
/-!
# Halász–Montgomery large values

This leaf develops the elementary Hilbert-space and exponential-sum argument
behind Iwaniec–Kowalski, Theorem 9.6.  The first unit is the finite-dimensional
duality step: the squared norm of a synthesis operator is controlled by the
largest absolute row sum of its Gram kernel.
-/
namespace MoltResearch
open Finset
noncomputable def halaszKernel (N : ℕ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ExpSums.e (-(u * Real.log n))

private axiom hm_sum_dyadic_tiling {A : Type*} [AddCommMonoid A]
    (V N J : ℕ) (f : ℕ → A) :
    ∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (min (2 ^ j * V) N) (min (2 ^ (j + 1) * V) N), f n
      = ∑ n ∈ Finset.Ioc (min V N) (min (2 ^ J * V) N), f n

private axiom sum_two_pow_add_one_range_le_five_halves (N : ℕ)
    (hN : 1 ≤ N) :
    ∑ j ∈ Finset.range (N.log2 + 1), (((2 ^ j + 1 : ℕ) : ℝ))
      ≤ (5 / 2 : ℝ) * (N : ℝ)

/-- A dyadic block with its van der Corput cost exposed.  Once the
Kusmin–Landau threshold holds, the square-root term disappears. -/
axiom norm_sum_e_neg_log_dyadic_block_le_split (v : ℝ) (M P : ℕ)
    (hv : 1 ≤ v) (hM : 1 ≤ M) (hMP : M ≤ P) (hP : P ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ioc M P, ExpSums.e (-(v * Real.log n))‖
      ≤ (if 13 * v ≤ 12 * (M + 1 : ℕ) then 0 else 22 * Real.sqrt v)
        + 12 * (M + 1 : ℕ) / v
/-- If `v ≤ 2T`, only `3(log(2T)+1)/2` binary blocks can lie before
the Kusmin–Landau threshold. -/
axiom card_pre_kusmin_blocks_le (J : ℕ) (v T : ℝ) (hT : 1 ≤ T)
    (hvT : v ≤ 2 * T) :
    (((Finset.range J).filter
        (fun j => 12 * ((2 ^ j + 1 : ℕ) : ℝ) < 13 * v)).card : ℝ)
      ≤ (3 / 2 : ℝ) * (Real.log (2 * T) + 1)


theorem norm_halaszKernel_of_one_le_of_le_two_mul (N : ℕ) (v T : ℝ)
    (hv : 1 ≤ v) (hvT : v ≤ 2 * T) (hT : 1 ≤ T) :
    ‖halaszKernel N v‖
      ≤ 1 + 30 * (N : ℝ) / v
        + 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
  classical
  by_cases hN0 : N = 0
  · subst N
    simp [halaszKernel]
    have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
    have hterm : 0 ≤ 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
      positivity
    linarith
  have hN : 1 ≤ N := by omega
  let J := N.log2 + 1
  let f : ℕ → ℂ := fun n => ExpSums.e (-(v * Real.log n))
  let B := (Finset.range J).filter
    (fun j => 12 * (((2 ^ j + 1 : ℕ) : ℝ)) < 13 * v)
  have hpowlt : N < 2 ^ J := by
    simp only [J]
    exact (Nat.log2_lt hN0).mp (Nat.lt_succ_self N.log2)
  have hpowle : 2 ^ N.log2 ≤ N := Nat.log2_self_le hN0
  have hMj : ∀ j ∈ Finset.range J, 2 ^ j ≤ N := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjle : j ≤ N.log2 := by simp only [J] at hj; omega
    exact (Nat.pow_le_pow_right (by norm_num) hjle).trans hpowle
  have htile : ∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n
      = ∑ n ∈ Finset.Ioc 1 N, f n := by
    have ht := hm_sum_dyadic_tiling 1 N J f
    have hleft : (∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (min (2 ^ j * 1) N)
              (min (2 ^ (j + 1) * 1) N), f n)
        = ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mul_one, mul_one, min_eq_left (hMj j hj)]
    rw [hleft] at ht
    have hmin1 : min 1 N = 1 := min_eq_left hN
    have hminN : min (2 ^ J * 1) N = N := by
      rw [mul_one, min_eq_right hpowlt.le]
    rwa [hmin1, hminN] at ht
  have hkernel : halaszKernel N v
      = f 1 + ∑ j ∈ Finset.range J,
          ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n := by
    rw [halaszKernel, Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons,
      ← htile]
  have hblock : ∀ j ∈ Finset.range J,
      ‖∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n‖
        ≤ (if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
            then 0 else 22 * Real.sqrt v)
          + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v := by
    intro j hj
    have hM := hMj j hj
    have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
    have hMP : 2 ^ j ≤ min (2 ^ (j + 1)) N := by
      exact le_min (by rw [hpow]; omega) hM
    have hP : min (2 ^ (j + 1)) N ≤ 2 * 2 ^ j := by
      exact (min_le_left _ _).trans_eq hpow
    exact norm_sum_e_neg_log_dyadic_block_le_split v (2 ^ j)
      (min (2 ^ (j + 1)) N) hv Nat.one_le_two_pow hMP hP
  have hsumNorm : ‖∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n‖
      ≤ ∑ j ∈ Finset.range J,
          ((if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
              then 0 else 22 * Real.sqrt v)
            + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v) := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hblock)
  have hBsum : ∑ j ∈ Finset.range J,
        (if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
          then 0 else 22 * Real.sqrt v)
      = 22 * Real.sqrt v * (B.card : ℝ) := by
    calc
      ∑ j ∈ Finset.range J,
          (if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
            then 0 else 22 * Real.sqrt v)
          = ∑ j ∈ B, 22 * Real.sqrt v := by
              simp only [B, Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro j _
              by_cases h : 12 * (((2 ^ j + 1 : ℕ) : ℝ)) < 13 * v
              · have hn : ¬ 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ)) :=
                  not_le.mpr h
                push_cast at h hn ⊢
                rw [if_neg hn, if_pos h]
              · have hl : 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ)) :=
                  le_of_not_gt h
                push_cast at h hl ⊢
                rw [if_pos hl, if_neg h]
      _ = 22 * Real.sqrt v * (B.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have htailSum : ∑ j ∈ Finset.range J,
        12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v
      = (12 / v) * ∑ j ∈ Finset.range J,
          (((2 ^ j + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsumForm : ∑ j ∈ Finset.range J,
          ((if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
              then 0 else 22 * Real.sqrt v)
            + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v)
      = 22 * Real.sqrt v * (B.card : ℝ)
          + (12 / v) * ∑ j ∈ Finset.range J,
              (((2 ^ j + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_add_distrib, hBsum, htailSum]
  have hBcard : (B.card : ℝ)
      ≤ (3 / 2 : ℝ) * (Real.log (2 * T) + 1) := by
    simpa only [B] using card_pre_kusmin_blocks_le J v T hT hvT
  have hroot : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
  have hpre : 22 * Real.sqrt v * (B.card : ℝ)
      ≤ 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
    have h := mul_le_mul_of_nonneg_left hBcard
      (show 0 ≤ 22 * Real.sqrt v by positivity)
    nlinarith
  have hA := sum_two_pow_add_one_range_le_five_halves N hN
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have htail : (12 / v) *
        (∑ j ∈ Finset.range (N.log2 + 1), (((2 ^ j + 1 : ℕ) : ℝ)))
      ≤ 30 * (N : ℝ) / v := by
    have h := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 12 / v)
    calc
      (12 / v) *
          (∑ j ∈ Finset.range (N.log2 + 1), (((2 ^ j + 1 : ℕ) : ℝ)))
          ≤ (12 / v) * ((5 / 2 : ℝ) * (N : ℝ)) := h
      _ = 30 * (N : ℝ) / v := by ring
  rw [hkernel]
  refine (norm_add_le _ _).trans ?_
  have hf1 : ‖f 1‖ = 1 := ExpSums.norm_e _
  rw [hf1]
  calc
    1 + ‖∑ j ∈ Finset.range J,
        ∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) N), f n‖
        ≤ 1 + ∑ j ∈ Finset.range J,
            ((if 13 * v ≤ 12 * (((2 ^ j + 1 : ℕ) : ℝ))
                then 0 else 22 * Real.sqrt v)
              + 12 * (((2 ^ j + 1 : ℕ) : ℝ)) / v) :=
          add_le_add le_rfl hsumNorm
    _ = 1 + 22 * Real.sqrt v * (B.card : ℝ)
          + (12 / v) * ∑ j ∈ Finset.range J,
              (((2 ^ j + 1 : ℕ) : ℝ)) := by rw [hsumForm]; ring
    _ ≤ 1 + 30 * (N : ℝ) / v
          + 33 * Real.sqrt v * (Real.log (2 * T) + 1) := by
      linarith

end MoltResearch
