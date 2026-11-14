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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_df81cc9ee18c6f17a739_FiniteWeightedGram ====
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
noncomputable def phaseAlign (z : ℂ) : ℂ := if z = 0 then 1 else conj z / ‖z‖


set_option linter.unusedVariables false in
theorem sum_norm_coefficient_vector_sq_le_gram
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (d : ι → ℂ) (e : κ → ι → ℂ) 
    (h_MathCollab_Density_Stronger_Atkinson_norm_sum_mul_sq_le : ∀ {ι : Type u_1} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ),
      ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2)
    (h_MathCollab_Density_Stronger_Atkinson_phaseAlign_mul : ∀ (z : ℂ), MathCollab.Density.Stronger.Atkinson.phaseAlign z * z = (↑‖z‖ : ℂ))
    (h_MathCollab_Density_Stronger_Atkinson_sum_norm_sq_sum_le_gram : ∀ {ι : Type u_1} {κ : Type u_2} [DecidableEq ι] [DecidableEq κ] (s : Finset ι) (W : Finset κ)
      (c : κ → ℂ) (y : κ → ι → ℂ),
      (∀ t ∈ W, ‖c t‖ ≤ 1) →
        ∑ n ∈ s, ‖∑ t ∈ W, c t * y t n‖ ^ 2 ≤
          ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, (starRingEnd ℂ : ℂ → ℂ) (y t n) * y u n‖)
    (h_MathCollab_Density_Stronger_Atkinson_norm_phaseAlign_le_one : ∀ (z : ℂ), ‖MathCollab.Density.Stronger.Atkinson.phaseAlign z‖ ≤ 1)
    :
    (∑ t ∈ W, ‖∑ n ∈ s, d n*e t n‖)^2 ≤
      (∑ n ∈ s, ‖d n‖^2)*
        ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ s, conj (e t n)*e u n‖ := by
  let D : κ → ℂ := fun t => ∑ n ∈ s, d n*e t n
  let c : κ → ℂ := fun t => phaseAlign (D t)
  have hc : ∀ t ∈ W, ‖c t‖ ≤ 1 := fun t _ => h_MathCollab_Density_Stronger_Atkinson_norm_phaseAlign_le_one (D t)
  have halign : ‖∑ t ∈ W, c t*D t‖ = ∑ t ∈ W, ‖D t‖ := by
    have he : (∑ t ∈ W, c t*D t) = ((∑ t ∈ W, ‖D t‖ : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl (fun t _ => h_MathCollab_Density_Stronger_Atkinson_phaseAlign_mul (D t))
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hexpand : (∑ t ∈ W, c t*D t) =
      ∑ n ∈ s, d n*(∑ t ∈ W, c t*e t n) := by
    simp only [D,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hcs := h_MathCollab_Density_Stronger_Atkinson_norm_sum_mul_sq_le s d (fun n => ∑ t ∈ W, c t*e t n)
  rw [← hexpand,halign] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (h_MathCollab_Density_Stronger_Atkinson_sum_norm_sq_sum_le_gram s W c e hc) (by positivity))
end MathCollab.Density.Stronger.Atkinson
