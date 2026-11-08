module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.TransportPrekopaLeindler
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.TransportHopfCoupling
public import Mathlib
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Filter Real
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace SKConstants.Transport
open WeakHessianTransport
set_option backward.isDefEq.respectTransparency false
def expPotentialLaw {ι : Type*} [Fintype ι] (U : EuclideanSpace ℝ ι → ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))
end SKConstants.Transport
