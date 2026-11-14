module

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_860946d7345609b1bd87_FiniteWeightedGram ====
-- Reversible module-visibility port of the audited development.
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Finset Set Filter
open scoped ComplexConjugate


set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson


set_option linter.unusedVariables false in
/-- The finite Gram-matrix bound underlying Halász--Montgomery duality. -/
theorem sum_norm_sq_sum_le_gram {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (c : κ → ℂ) (y : κ → ι → ℂ)
    (hc : ∀ t ∈ W, ‖c t‖ ≤ 1) 
    (h_MathCollab_Density_Stronger_Atkinson_norm_conj_eq : ∀ (z : ℂ), ‖(starRingEnd ℂ : ℂ → ℂ) z‖ = ‖z‖)
    :
    (∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (y t n) * y u n‖ := by
  have hexpand :
      ((∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
        ∑ t ∈ W, ∑ u ∈ W,
          conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n) := by
    have hpoint (n : ι) :
        ((‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
          conj (∑ t ∈ W, c t * y t n) * (∑ t ∈ W, c t * y t n) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    have hcast :
        ((∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) =
          ∑ n ∈ s, ((‖∑ t ∈ W, c t * y t n‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast]
    simp_rw [hpoint]
    simp only [map_sum, map_mul]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hre := congrArg Complex.re hexpand
  simp only [ofReal_re] at hre
  rw [hre]
  calc
    Complex.re (∑ t ∈ W, ∑ u ∈ W,
        conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)) ≤
        ‖∑ t ∈ W, ∑ u ∈ W,
          conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖conj (c t) * c u * (∑ n ∈ s, conj (y t n) * y u n)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun t ht => norm_sum_le _ _)
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        ‖∑ n ∈ s, conj (y t n) * y u n‖ := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, norm_mul]
      rw [h_MathCollab_Density_Stronger_Atkinson_norm_conj_eq]
      have hct := hc t ht
      have hcu := hc u hu
      have hprod : ‖c t‖ * ‖c u‖ ≤ 1 := by
        calc
          ‖c t‖ * ‖c u‖ ≤ 1 * 1 :=
            mul_le_mul hct hcu (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      exact (mul_le_mul_of_nonneg_right hprod
        (norm_nonneg (∑ n ∈ s, conj (y t n) * y u n))).trans_eq (one_mul _)

end MathCollab.Density.Stronger.Atkinson
