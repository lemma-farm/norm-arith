module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Set.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Tactic.Positivity
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.InnerProductSpace.Calculus

-- ==== Examples.djalilchafai__ginibre_poincare.Examples.Example_2fa2a127c2386bb30ab0_MatrixSpatialCutoff ====
@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev MatrixRealSpace (n : ℕ) := Fin n → Fin n → ℂ
def matrixSpatialBump (n : ℕ) : ContDiffBump (0 : MatrixRealSpace n) :=
  ⟨1, 2, by norm_num, by norm_num⟩
def matrixSpatialCutoff (n k : ℕ) (A : MatrixRealSpace n) : ℝ :=
  matrixSpatialBump n (((k : ℝ) + 1)⁻¹ • A)

set_option linter.unusedVariables false in
theorem matrixSpatialCutoff_derivative_bound (n : ℕ) 
    (h_GinibrePoincare_matrixSpatialCutoff_fderiv : ∀ (n k : ℕ) (A H : GinibrePoincare.MatrixRealSpace n),
      (fderiv ℝ (GinibrePoincare.matrixSpatialCutoff n k) A : GinibrePoincare.MatrixRealSpace n → ℝ) H =
        ((↑k : ℝ) + 1)⁻¹ *
          (fderiv ℝ (↑(GinibrePoincare.matrixSpatialBump n) : GinibrePoincare.MatrixRealSpace n → ℝ)
                (((↑k : ℝ) + 1)⁻¹ • A) :
              GinibrePoincare.MatrixRealSpace n → ℝ)
            H)
    :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (A H : MatrixRealSpace n),
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M / ((k : ℝ) + 1) * ‖H‖ := by
  obtain ⟨M, hM⟩ := ((matrixSpatialBump n).contDiff (n := 1)).continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support ((matrixSpatialBump n).hasCompactSupport.fderiv ℝ)
  refine ⟨M, (norm_nonneg _).trans (hM 0), ?_⟩
  intro k A H
  rw [h_GinibrePoincare_matrixSpatialCutoff_fderiv, abs_mul, abs_of_nonneg (by positivity)]
  have hnorm := (fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
    (((k : ℝ) + 1)⁻¹ • A)).le_opNorm H
  have hh : |fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
      (((k : ℝ) + 1)⁻¹ • A) H| ≤ M * ‖H‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg H))
  calc
    _ ≤ ((k : ℝ) + 1)⁻¹ * (M * ‖H‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring
end
end GinibrePoincare
