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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_5f574360490226919216_PrefixMean ====
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
theorem integral_norm_sq_dirichletPrefix_le
    (M : ℕ) (a : ℕ → ℂ) {A B L : ℝ} (hAB : A ≤ B)
    (hone : ‖a 1‖^2 ≤ L)
    (hcoeff : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖a n‖^2) ≤ L) 
    (h_MathCollab_Density_Stronger_Fourth_integral_norm_sq_dirichletTime_interval_le : ∀ (N : ℕ) (a : ℕ → ℂ) {A B : ℝ},
      0 < N →
        A ≤ B →
          ∫ (t : ℝ) in A..B, ‖MathCollab.Density.Stronger.Fourth.dirichletTime N a t‖ ^ 2 ≤
            (B - A + 2 * (5 * Real.pi + 1) * (↑N : ℝ)) * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2)
    (h_MathCollab_Density_Stronger_Fourth_integral_norm_sq_dirichletPrefix_le_blocks : ∀ (M : ℕ) (a : ℕ → ℂ) {A B : ℝ},
      A ≤ B →
        ∫ (t : ℝ) in A..B, ‖MathCollab.Density.Stronger.Fourth.dirichletPrefix (2 ^ M) a t‖ ^ 2 ≤
          2 * ((↑M : ℝ) + 1) *
            ((B - A) * ‖a 1‖ ^ 2 +
              ∑ j ∈ Finset.range M,
                ∫ (t : ℝ) in A..B, ‖MathCollab.Density.Stronger.Fourth.dirichletTime (2 ^ j) a t‖ ^ 2))
    :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)^2*(B-A+2*(5*Real.pi+1)*(2:ℝ)^M)*L := by
  have hL : 0 ≤ L := (sq_nonneg ‖a 1‖).trans hone
  have hT : 0 ≤ B-A := sub_nonneg.mpr hAB
  let E : ℝ := (B-A+2*(5*Real.pi+1)*(2:ℝ)^M)*L
  have hfirst : (B-A)*‖a 1‖^2 ≤ E := by
    dsimp [E]
    apply mul_le_mul (le_add_of_nonneg_right (by positivity)) hone (sq_nonneg _)
    positivity
  have hblock : ∀ j ∈ Finset.range M,
      (∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) ≤ E := by
    intro j hj
    have hjM : j ≤ M := (Finset.mem_range.mp hj).le
    have hp : ((2^j:ℕ):ℝ) ≤ (2:ℝ)^M := by
      norm_cast
      exact pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) hjM
    apply (h_MathCollab_Density_Stronger_Fourth_integral_norm_sq_dirichletTime_interval_le (2^j) a
      (by positivity) hAB).trans
    dsimp [E]
    apply mul_le_mul (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hp (by positivity)))
      (hcoeff j hj) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    positivity
  have hsum : (∑ j ∈ Finset.range M,
      ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) ≤ (M:ℝ)*E := by
    simpa using Finset.sum_le_sum hblock
  calc
    _ ≤ 2*((M:ℝ)+1)*((B-A)*‖a 1‖^2+
        ∑ j ∈ Finset.range M, ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) :=
      h_MathCollab_Density_Stronger_Fourth_integral_norm_sq_dirichletPrefix_le_blocks M a hAB
    _ ≤ 2*((M:ℝ)+1)*((M:ℝ)+1)*E := by
      rw [mul_assoc (2*((M:ℝ)+1))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = _ := by dsimp [E]; ring
end MathCollab.Density.Stronger.Fourth
