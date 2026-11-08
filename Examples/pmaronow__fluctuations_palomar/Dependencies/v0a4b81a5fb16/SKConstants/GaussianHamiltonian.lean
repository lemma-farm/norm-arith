module
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.SKModel
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GibbsComparison
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.ConcentrationMGF
public import Mathlib
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
namespace SKConstants
@[expose] def goeSpinHamiltonian {n : ℕ} (sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  quadraticHamiltonian (GaussianProposal.goeMatrix sigma z) x
end SKConstants
