module
public import Mathlib
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SKConstants.GaussianProposal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The actual primitive finite standard Gaussian measure. -/
@[expose] def primitiveGaussian (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) := stdGaussian (EuclideanSpace ℝ ι)
instance : IsProbabilityMeasure (primitiveGaussian ι) := by
  unfold primitiveGaussian
  infer_instance
instance : IsGaussian (primitiveGaussian ι) := by
  unfold primitiveGaussian
  infer_instance
@[expose] def goeMatrix (sigma : ℝ) (z : EuclideanSpace ℝ (ι × ι)) : Matrix ι ι ℝ :=
  fun i j => sigma * (z (i,j) + z (j,i))
end SKConstants.GaussianProposal
