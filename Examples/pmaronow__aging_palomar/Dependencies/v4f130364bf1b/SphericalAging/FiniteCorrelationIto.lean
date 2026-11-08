module
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.HamiltonianDerivativeCovariance
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.RadialUniqueness
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.BoundedItoMultiplier
set_option autoImplicit false
public section
/-! Actual finite-N empirical correlation coefficients and full-filtration
martingale. The noise is constructed from the projected Brownian integrands,
and its dimension-dependent variance bound is proved by genuine Itô isometry.
These are prerequisites of the finite-N CK bridge, not a convergence theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.FiniteCorrelationIto
open HardSphereDynamics FiniteModel LandscapeDerivatives VectorIto
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
section Process
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
  {X : ℝ≥0 → Ω → State N}
end Process
end SphericalAging.FiniteCorrelationIto
