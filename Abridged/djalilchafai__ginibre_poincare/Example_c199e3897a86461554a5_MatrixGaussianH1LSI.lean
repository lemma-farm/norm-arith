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

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v363a8b4b3804.GinibrePoincare.Analysis.MatrixSpatialCutoff ====
public section
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

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Examples.Example_c199e3897a86461554a5_MatrixGaussianH1LSI ====
@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
def matrixSpatialTruncation (n k : ℕ) (F : MatrixRealSpace n → ℝ) : MatrixRealSpace n → ℝ :=
  fun A => matrixSpatialCutoff n k A * F A


set_option linter.unusedVariables false in
theorem matrixSpatialTruncation_L2_errors (n : ℕ) (μ : Measure (MatrixRealSpace n))
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F) (hv : MemLp F 2 μ)
    (H : MatrixRealSpace n) (hD : MemLp (fun A => fderiv ℝ F A H) 2 μ) 
    (h_GinibrePoincare_matrixSpatialTruncation_fderiv : ∀ (n k : ℕ) (F : GinibrePoincare.MatrixRealSpace n → ℝ),
      ContDiff ℝ 1 F →
        ∀ (A H : GinibrePoincare.MatrixRealSpace n),
          (fderiv ℝ (GinibrePoincare.matrixSpatialTruncation n k F) A :
                GinibrePoincare.MatrixRealSpace n → ℝ)
              H =
            (fderiv ℝ (GinibrePoincare.matrixSpatialCutoff n k) A :
                    GinibrePoincare.MatrixRealSpace n → ℝ)
                  H *
                F A +
              GinibrePoincare.matrixSpatialCutoff n k A *
                (fderiv ℝ F A : GinibrePoincare.MatrixRealSpace n → ℝ) H)
    (h_GinibrePoincare_matrixSpatialCutoff_derivative_bound : ∀ (n : ℕ),
      ∃ (M : ℝ),
        0 ≤ M ∧
          ∀ (k : ℕ) (A H : GinibrePoincare.MatrixRealSpace n),
            |(fderiv ℝ (GinibrePoincare.matrixSpatialCutoff n k) A :
                    GinibrePoincare.MatrixRealSpace n → ℝ)
                  H| ≤
              M / ((↑k : ℝ) + 1) * ‖H‖)
    (h_GinibrePoincare_matrixSpatialTruncation_limits : ∀ (n : ℕ) (F : GinibrePoincare.MatrixRealSpace n → ℝ),
      ContDiff ℝ 1 F →
        ∀ (A H : GinibrePoincare.MatrixRealSpace n),
          Filter.Tendsto (fun (k : ℕ) ↦ GinibrePoincare.matrixSpatialTruncation n k F A) Filter.atTop
              (nhds (F A)) ∧
            Filter.Tendsto
              (fun (k : ℕ) ↦
                (fderiv ℝ (GinibrePoincare.matrixSpatialTruncation n k F) A :
                    GinibrePoincare.MatrixRealSpace n → ℝ)
                  H)
              Filter.atTop (nhds ((fderiv ℝ F A : GinibrePoincare.MatrixRealSpace n → ℝ) H)))
    (h_GinibrePoincare_matrixSpatialCutoff_mem_unit : ∀ (n k : ℕ) (A : GinibrePoincare.MatrixRealSpace n),
      0 ≤ GinibrePoincare.matrixSpatialCutoff n k A ∧ GinibrePoincare.matrixSpatialCutoff n k A ≤ 1)
    (h_GinibrePoincare_matrixSpatialTruncation_contDiff : ∀ (n k : ℕ) (F : GinibrePoincare.MatrixRealSpace n → ℝ),
      ContDiff ℝ 1 F → ContDiff ℝ 1 (GinibrePoincare.matrixSpatialTruncation n k F))
    :
    Tendsto (fun k => ∫ A, (matrixSpatialTruncation n k F A - F A) ^ 2 ∂μ)
      atTop (nhds 0) ∧
    Tendsto (fun k => ∫ A,
      (fderiv ℝ (matrixSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ∂μ)
      atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := h_GinibrePoincare_matrixSpatialCutoff_derivative_bound n
  have hb (k : ℕ) (A : MatrixRealSpace n) :
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M * ‖H‖ := by
    refine (hM k A H).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg H))
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · have ht := tendsto_integral_of_dominated_convergence (fun A => F A ^ 2)
      (fun k => (((h_GinibrePoincare_matrixSpatialTruncation_contDiff n k F hF).continuous.sub hF.continuous).pow 2).aestronglyMeasurable)
      hv.integrable_sq (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (matrixSpatialCutoff n k A * F A - F A) ^ 2 ≤ F A ^ 2
        obtain ⟨h0, h1⟩ := h_GinibrePoincare_matrixSpatialCutoff_mem_unit n k A
        have hc : (matrixSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (F A))])
      (ae_of_all _ fun A => by simpa using
        (((h_GinibrePoincare_matrixSpatialTruncation_limits n F hF A H).1.sub_const (F A)).pow 2))
    simpa using ht
  · have ht := tendsto_integral_of_dominated_convergence
      (fun A => 2 * (M * ‖H‖) ^ 2 * F A ^ 2 + 2 * (fderiv ℝ F A H) ^ 2)
      (fun k => (((((h_GinibrePoincare_matrixSpatialTruncation_contDiff n k F hF).continuous_fderiv one_ne_zero).clm_apply
        continuous_const).sub ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)).pow 2).aestronglyMeasurable)
      ((hv.integrable_sq.const_mul (2 * (M * ‖H‖) ^ 2)).add (hD.integrable_sq.const_mul 2))
      (fun k => ae_of_all _ fun A => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        change (fderiv ℝ (matrixSpatialTruncation n k F) A H - fderiv ℝ F A H) ^ 2 ≤ _
        rw [h_GinibrePoincare_matrixSpatialTruncation_fderiv n k F hF]
        obtain ⟨hc0, hc1⟩ := h_GinibrePoincare_matrixSpatialCutoff_mem_unit n k A
        have hc2 : (matrixSpatialCutoff n k A - 1) ^ 2 ≤ 1 := by nlinarith
        have hd2 : (fderiv ℝ (matrixSpatialCutoff n k) A H) ^ 2 ≤ (M * ‖H‖) ^ 2 := by
          have hh := hb k A
          nlinarith [sq_abs (fderiv ℝ (matrixSpatialCutoff n k) A H),
            abs_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H), mul_nonneg hM0 (norm_nonneg H)]
        have hx := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (F A))
        have hy := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (fderiv ℝ F A H))
        nlinarith [sq_nonneg (fderiv ℝ (matrixSpatialCutoff n k) A H * F A -
          (matrixSpatialCutoff n k A - 1) * fderiv ℝ F A H)])
      (ae_of_all _ fun A => by simpa using
        (((h_GinibrePoincare_matrixSpatialTruncation_limits n F hF A H).2.sub_const (fderiv ℝ F A H)).pow 2))
    simpa using ht
end
end GinibrePoincare
