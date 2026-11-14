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

-- ==== Examples.ProofFleet__prooffleet.Examples.Example_7178b1b61fb181bd4a4b_HalaszMontgomeryLargeValues ====
/-!
# Halász–Montgomery large values

This leaf develops the elementary Hilbert-space and exponential-sum argument
behind Iwaniec–Kowalski, Theorem 9.6.  The first unit is the finite-dimensional
duality step: the squared norm of a synthesis operator is controlled by the
largest absolute row sum of its Gram kernel.
-/
namespace MoltResearch
open Finset
/-- Schur's symmetric-kernel estimate for finite real families. -/
theorem sum_mul_mul_le_sum_sq_mul_row_sum_of_symm {κ : Type*}
    (J : Finset κ) (x : κ → ℝ) (K : κ → κ → ℝ)
    (hK0 : ∀ t s, 0 ≤ K t s) (hKsymm : ∀ t s, K t s = K s t) :
    ∑ t ∈ J, ∑ s ∈ J, x t * x s * K t s
      ≤ ∑ t ∈ J, x t ^ 2 * ∑ s ∈ J, K t s := by
  classical
  have hstep : ∀ t s, x t * x s * K t s
      ≤ ((x t ^ 2 + x s ^ 2) / 2) * K t s := by
    intro t s
    refine mul_le_mul_of_nonneg_right ?_ (hK0 t s)
    nlinarith [sq_nonneg (x t - x s)]
  refine le_trans (Finset.sum_le_sum fun t _ =>
    Finset.sum_le_sum fun s _ => hstep t s) ?_
  have hsplit : ∑ t ∈ J, ∑ s ∈ J, ((x t ^ 2 + x s ^ 2) / 2) * K t s
      = (∑ t ∈ J, ∑ s ∈ J, (x t ^ 2 / 2) * K t s)
        + ∑ t ∈ J, ∑ s ∈ J, (x s ^ 2 / 2) * K t s := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hswap : ∑ t ∈ J, ∑ s ∈ J, (x s ^ 2 / 2) * K t s
      = ∑ t ∈ J, ∑ s ∈ J, (x t ^ 2 / 2) * K t s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hKsymm s t]
  rw [hsplit, hswap]
  have hcollect : (∑ t ∈ J, ∑ s ∈ J, (x t ^ 2 / 2) * K t s)
      + ∑ t ∈ J, ∑ s ∈ J, (x t ^ 2 / 2) * K t s
      = ∑ t ∈ J, x t ^ 2 * ∑ s ∈ J, K t s := by
    rw [← two_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  exact le_of_eq hcollect

/-! ## The logarithmic Dirichlet kernel -/

/-! ## Well-spaced kernel rows -/

/-! ## The absolute-constant ledger -/

end MoltResearch
