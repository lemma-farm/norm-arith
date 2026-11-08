module
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.HardSphereDynamics
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.FourPapersCommon.FilteredItoContinuous
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Tactic
set_option autoImplicit false
public section
/-!
# Full-filtration finite-dimensional stochastic integration

The driving data include joint increment independence from the complete
filtration. VectorBrownian constructs these data on the actual product
continuous-path law, also with independent initial point and disorder.
The cross-coordinate identities below are proved for the constructed
Brownian integrals; they are not radial Itô identities supplied as hypotheses.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorIto
open HardSphereDynamics
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
end SphericalAging.VectorIto
