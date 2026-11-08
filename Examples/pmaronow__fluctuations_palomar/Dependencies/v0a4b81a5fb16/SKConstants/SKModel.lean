module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GaussianProposal
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.HeatBathMeasurability
public import Mathlib
public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SKConstants
theorem continuous_goeMatrix {V : Type*} [Fintype V] [DecidableEq V] (sigma : ℝ) :
    Continuous (GaussianProposal.goeMatrix (ι := V) sigma) := by
  unfold GaussianProposal.goeMatrix
  fun_prop
/-- The paper's completed SK disorder, with off-diagonal variance `1/n`
and diagonal variance `2/n` for positive `n`. -/
@[expose] def skDisorderLaw (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
    (GaussianProposal.goeMatrix (1 / Real.sqrt (((2 : ℕ) : ℝ) * (n : ℝ))))
instance skDisorderLaw_isProbability (n : ℕ) : IsProbabilityMeasure (skDisorderLaw n) := by
  unfold skDisorderLaw
  infer_instance
@[expose] def skJointLaw (n : ℕ) (beta : ℝ) :
    Measure (Matrix (Fin n) (Fin n) ℝ × Spin n) := jointGibbsMeasure beta (skDisorderLaw n)
instance skJointLaw_isProbability (n : ℕ) (beta : ℝ) :
    IsProbabilityMeasure (skJointLaw n beta) := by unfold skJointLaw; infer_instance
end SKConstants
