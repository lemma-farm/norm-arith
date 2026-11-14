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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.vff363806cf85.MathCollab.Density.Stronger.Fourth.MeanValueCore ====
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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_eb781e225d4bce2cf0dc_PrefixMean ====
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
theorem integral_norm_sq_dirichletPrefix_le_blocks
    (M : ℕ) (a : ℕ → ℂ) {A B : ℝ} (hAB : A ≤ B) 
    (h_MathCollab_Density_Stronger_Fourth_continuous_dirichletPrefix : ∀ (N : ℕ) (a : ℕ → ℂ), Continuous (MathCollab.Density.Stronger.Fourth.dirichletPrefix N a))
    (h_MathCollab_Density_Stronger_Fourth_continuous_dirichletTime : ∀ (N : ℕ) (a : ℕ → ℂ), Continuous (MathCollab.Density.Stronger.Fourth.dirichletTime N a))
    (h_MathCollab_Density_Stronger_Fourth_norm_dirichletPrefix_pow_two_sq_le : ∀ (M : ℕ) (a : ℕ → ℂ) (t : ℝ),
      ‖MathCollab.Density.Stronger.Fourth.dirichletPrefix (2 ^ M) a t‖ ^ 2 ≤
        2 * ((↑M : ℝ) + 1) *
          (‖a 1‖ ^ 2 +
            ∑ j ∈ Finset.range M, ‖MathCollab.Density.Stronger.Fourth.dirichletTime (2 ^ j) a t‖ ^ 2))
    :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)*((B-A)*‖a 1‖^2+
        ∑ j ∈ Finset.range M, ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) := by
  have hi (j : ℕ) : IntervalIntegrable
      (fun t : ℝ => ‖dirichletTime (2^j) a t‖^2) volume A B :=
    ((h_MathCollab_Density_Stronger_Fourth_continuous_dirichletTime (2^j) a).norm.pow 2).intervalIntegrable A B
  have hsum : IntervalIntegrable
      (fun t : ℝ => ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) volume A B := by
    convert IntervalIntegrable.sum (Finset.range M) (fun j _ => hi j) using 1
    ext t
    simp
  have hconst : IntervalIntegrable (fun _ : ℝ => ‖a 1‖^2) volume A B :=
    intervalIntegrable_const
  calc
    _ ≤ ∫ t : ℝ in A..B,
        2*((M:ℝ)+1)*(‖a 1‖^2+
          ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) :=
      intervalIntegral.integral_mono_on hAB
        (((h_MathCollab_Density_Stronger_Fourth_continuous_dirichletPrefix (2^M) a).norm.pow 2).intervalIntegrable A B)
        ((hconst.add hsum).const_mul _)
        (fun t _ => h_MathCollab_Density_Stronger_Fourth_norm_dirichletPrefix_pow_two_sq_le M a t)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hconst hsum,
        intervalIntegral.integral_const,
        intervalIntegral.integral_finsetSum (fun j _ => hi j)]
      rfl

end MathCollab.Density.Stronger.Fourth
