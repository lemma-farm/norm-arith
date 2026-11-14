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

end ExpSums
end MoltResearch

end

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_ae9f90a120a9cc640efe_HalaszMontgomeryLargeValues ====
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


set_option linter.unusedVariables false in
/-- **H-4, the constant `64`.**  The refined kernel ledger closes the
well-spaced row at the exact constant used by the interface. -/
theorem sum_norm_halaszKernel_sub_le_sixty_four (N : ℕ) (T : ℝ)
    (𝒯 : Finset ℝ) (t : ℝ) (hT : 1 ≤ T) (ht : t ∈ 𝒯)
    (hrange : ∀ s ∈ 𝒯, |s| ≤ T)
    (hsep : ∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) 
    (h_MoltResearch_sum_inv_abs_sub_erase_le : ∀ (T : ℝ) (𝒯 : Finset ℝ) (t : ℝ),
      1 ≤ T →
        t ∈ 𝒯 →
          (∀ s ∈ 𝒯, |s| ≤ T) →
            (∀ s ∈ 𝒯, ∀ u ∈ 𝒯, s ≠ u → 1 ≤ |s - u|) →
              ∑ s ∈ 𝒯.erase t, 1 / |t - s| ≤ 2 * (Real.log (2 * T) + 1))
    (h_MoltResearch_norm_halaszKernel_le_of_abs_le_two_mul : ∀ (N : ℕ) (u T : ℝ),
      1 ≤ |u| →
        |u| ≤ 2 * T →
          1 ≤ T →
            ‖MoltResearch.halaszKernel N u‖ ≤
              1 + 30 * (↑N : ℝ) / |u| + 33 * √|u| * (Real.log (2 * T) + 1))
    (h_MoltResearch_sum_sqrt_abs_sub_erase_le : ∀ (T : ℝ) (𝒯 : Finset ℝ),
      ∀ t ∈ 𝒯, (∀ s ∈ 𝒯, |s| ≤ T) → ∑ s ∈ 𝒯.erase t, √|t - s| ≤ (↑𝒯.card : ℝ) * √(2 * T))
    (h_MoltResearch_norm_halaszKernel_zero : ∀ (N : ℕ), ‖MoltResearch.halaszKernel N 0‖ = (↑N : ℝ))
    :
    ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      ≤ 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
        * (Real.log (2 * T) + 1) := by
  classical
  let L := Real.log (2 * T) + 1
  have hlog : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hL1 : 1 ≤ L := by simp only [L]; linarith
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hsT1 : 1 ≤ Real.sqrt T := by
    have hs := Real.sqrt_le_sqrt hT
    simpa using hs
  have hsT0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have hs2sq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs20 := Real.sqrt_nonneg 2
    nlinarith
  have hs2T : Real.sqrt (2 * T) ≤ (3 / 2 : ℝ) * Real.sqrt T := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hs2 hsT0
  have hdiag : ‖halaszKernel N (t - t)‖ = (N : ℝ) := by
    simpa using h_MoltResearch_norm_halaszKernel_zero N
  have hoff : ∀ s ∈ 𝒯.erase t,
      ‖halaszKernel N (t - s)‖
        ≤ 1 + 30 * (N : ℝ) / |t - s| + 33 * Real.sqrt |t - s| * L := by
    intro s hs
    have hsMem : s ∈ 𝒯 := Finset.mem_of_mem_erase hs
    have hne : t ≠ s := ne_comm.mp (Finset.ne_of_mem_erase hs)
    have hgap := hsep t ht s hsMem hne
    have hgapT : |t - s| ≤ 2 * T := by
      have htlo := (abs_le.mp (hrange t ht)).1
      have hthi := (abs_le.mp (hrange t ht)).2
      have hslo := (abs_le.mp (hrange s hsMem)).1
      have hshi := (abs_le.mp (hrange s hsMem)).2
      rw [abs_le]
      constructor <;> linarith
    simpa only [L] using
      h_MoltResearch_norm_halaszKernel_le_of_abs_le_two_mul N (t - s) T hgap hgapT hT
  have hoffsum : ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖
      ≤ ((𝒯.erase t).card : ℝ)
        + 30 * (N : ℝ) * (∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|)
        + 33 * L * (∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|) := by
    refine (Finset.sum_le_sum hoff).trans_eq ?_
    have hA : ∑ s ∈ 𝒯.erase t, 30 * (N : ℝ) / |t - s|
        = 30 * (N : ℝ) *
          (∑ s ∈ 𝒯.erase t, (1 : ℝ) / |t - s|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    have hB : ∑ s ∈ 𝒯.erase t, 33 * Real.sqrt |t - s| * L
        = 33 * L * (∑ s ∈ 𝒯.erase t, Real.sqrt |t - s|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, hA, hB]
  have hinv := h_MoltResearch_sum_inv_abs_sub_erase_le T 𝒯 t hT ht hrange hsep
  have hsqrt := h_MoltResearch_sum_sqrt_abs_sub_erase_le T 𝒯 t ht hrange
  have hcardNat : (𝒯.erase t).card ≤ 𝒯.card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  have hcard : ((𝒯.erase t).card : ℝ) ≤ (𝒯.card : ℝ) := by
    exact_mod_cast hcardNat
  have hinvScaled := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ 30 * (N : ℝ) by positivity)
  have hsqrtScaled := mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ 33 * L by positivity)
  have hofffinal : ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖
      ≤ (𝒯.card : ℝ) + 60 * (N : ℝ) * L
        + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T)) := by
    refine hoffsum.trans ?_
    simp only [L] at hinvScaled ⊢
    linarith
  have hsplit : ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      = ‖halaszKernel N (t - t)‖
        + ∑ s ∈ 𝒯.erase t, ‖halaszKernel N (t - s)‖ := by
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ ht).symm
  have hrow : ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
      ≤ (N : ℝ) + ((𝒯.card : ℝ) + 60 * (N : ℝ) * L
        + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))) := by
    rw [hsplit, hdiag]
    linarith
  have hNpart : (N : ℝ) + 60 * (N : ℝ) * L
      ≤ 64 * (N : ℝ) * L := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hL1)]
  have hrootScaled : 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))
      ≤ (99 / 2 : ℝ) * (𝒯.card : ℝ) * Real.sqrt T * L := by
    have hc0 : (0 : ℝ) ≤ (𝒯.card : ℝ) := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_left hs2T
      (show 0 ≤ 33 * L * (𝒯.card : ℝ) by positivity)
    nlinarith
  have honeSL : (1 : ℝ) ≤ Real.sqrt T * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsT1) (sub_nonneg.mpr hL1)]
  have hcardUnit : (𝒯.card : ℝ)
      ≤ (𝒯.card : ℝ) * Real.sqrt T * L := by
    have hc0 : (0 : ℝ) ≤ (𝒯.card : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr honeSL)]
  have hCpart : (𝒯.card : ℝ)
        + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))
      ≤ 64 * (𝒯.card : ℝ) * Real.sqrt T * L := by
    linarith
  calc
    ∑ s ∈ 𝒯, ‖halaszKernel N (t - s)‖
        ≤ (N : ℝ) + ((𝒯.card : ℝ) + 60 * (N : ℝ) * L
          + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))) := hrow
    _ = ((N : ℝ) + 60 * (N : ℝ) * L)
          + ((𝒯.card : ℝ)
            + 33 * L * ((𝒯.card : ℝ) * Real.sqrt (2 * T))) := by ring
    _ ≤ 64 * (N : ℝ) * L
          + 64 * (𝒯.card : ℝ) * Real.sqrt T * L :=
      add_le_add hNpart hCpart
    _ = 64 * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T)
          * (Real.log (2 * T) + 1) := by simp only [L]; ring
end MoltResearch
