module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp

-- ==== Examples.pmaronow__fluctuations_palomar.Examples.Example_516aa16a73ca2c98ee8c_GaussianPrimitiveLift ====
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option maxHeartbeats 800000
namespace SKConstants.GaussianProposal
section Involution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
def involutionSym (U : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E :=
  (1/2 : ℝ) • (ContinuousLinearMap.id ℝ E+U.toContinuousLinearEquiv.toContinuousLinearMap)
def involutionAnti (U : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E :=
  (1/2 : ℝ) • (ContinuousLinearMap.id ℝ E-U.toContinuousLinearEquiv.toContinuousLinearMap)
lemma involution_parts_norm_sq (U : E ≃ₗᵢ[ℝ] E) (t : E) :
    ‖involutionSym U t‖^2+‖involutionAnti U t‖^2 = ‖t‖^2 := by
  change ‖(1/2 : ℝ) • (t+U t)‖^2+‖(1/2 : ℝ) • (t-U t)‖^2 = _
  rw [norm_smul,norm_smul,mul_pow,mul_pow,norm_add_sq_real,norm_sub_sq_real,U.norm_map]
  norm_num
  ring

end Involution
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SKConstants.GaussianProposal
