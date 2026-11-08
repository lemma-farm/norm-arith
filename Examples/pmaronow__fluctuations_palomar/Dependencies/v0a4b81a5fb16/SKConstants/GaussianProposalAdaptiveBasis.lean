module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GaussianProposalRevelation
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GaussianProposalAdaptiveKernel
import Mathlib
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SKConstants.GaussianProposal
variable {ι Past : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace Past]
@[expose] def gaussianUpperLaw (sigma : ℝ) (ι : Type*) [Fintype ι] [LinearOrder ι] :
    Measure (UpperPair ι → ℝ) :=
  Measure.pi (fun p : UpperPair ι => gaussianReal 0
    (if p.1.1 = p.1.2 then (((4 : ℕ) : ℝ) * sigma ^ 2).toNNReal else (((2 : ℕ) : ℝ) * sigma ^ 2).toNNReal))
instance (sigma : ℝ) : IsProbabilityMeasure (gaussianUpperLaw sigma ι) := by
  unfold gaussianUpperLaw
  infer_instance
end SKConstants.GaussianProposal
