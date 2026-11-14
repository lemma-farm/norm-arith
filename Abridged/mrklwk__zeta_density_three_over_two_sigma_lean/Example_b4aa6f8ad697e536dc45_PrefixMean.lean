module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic
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
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.vc52a14ebc9b3.MathCollab.Density.Stronger.Fourth.MeanValueCore ====
public section
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

/-- The `dirichletTime` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def dirichletTime (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))

end MathCollab.Density.Stronger.Fourth

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_b4aa6f8ad697e536dc45_PrefixMean ====
-- Reversible module-visibility port of the audited development.
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Complex Set Finset MeasureTheory Filter
open scoped BigOperators Interval ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Fourth

def dirichletPrefix (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, a n*Complex.exp (-(I*(t:ℂ)*(Real.log n:ℂ)))


set_option linter.unusedVariables false in
theorem norm_dirichletPrefix_pow_two_sq_le (M : ℕ) (a : ℕ → ℂ) (t : ℝ) 
    (h_MathCollab_Density_Stronger_Fourth_dirichletPrefix_pow_two : ∀ (M : ℕ) (a : ℕ → ℂ) (t : ℝ),
      MathCollab.Density.Stronger.Fourth.dirichletPrefix (2 ^ M) a t =
        a 1 + ∑ j ∈ Finset.range M, MathCollab.Density.Stronger.Fourth.dirichletTime (2 ^ j) a t)
    (h_MathCollab_Density_Stronger_Fourth_norm_sum_mul_sq_le : ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ),
      ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2)
    :
    ‖dirichletPrefix (2^M) a t‖^2 ≤
      2*((M:ℝ)+1)*(‖a 1‖^2+∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) := by
  let S : ℂ := ∑ j ∈ Finset.range M, dirichletTime (2^j) a t
  let Q : ℝ := ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : ‖S‖^2 ≤ (M:ℝ)*Q := by
    simpa [S,Q] using h_MathCollab_Density_Stronger_Fourth_norm_sum_mul_sq_le (Finset.range M)
      (fun _ => (1:ℂ)) (fun j => dirichletTime (2^j) a t)
  rw [h_MathCollab_Density_Stronger_Fourth_dirichletPrefix_pow_two]
  change ‖a 1+S‖^2 ≤ 2*((M:ℝ)+1)*(‖a 1‖^2+Q)
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (a 1) S) 2
  have hM : 0 ≤ (M:ℝ) := Nat.cast_nonneg M
  nlinarith [sq_nonneg (‖a 1‖-‖S‖),mul_nonneg hM (sq_nonneg ‖a 1‖)]
end MathCollab.Density.Stronger.Fourth
