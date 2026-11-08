module
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.VectorQuadraticVariation
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.StochasticCalculus.WeightedBracketRiemann
set_option autoImplicit false
public section
/-!
# Itô's formula for the constructed Brownian vector in its full filtration

The predictable diffusion is the actual finite family of integrands, and
its bracket is proved from the realized independent Brownian drivers.
The formula characterizes the space integral by its left partition sums.
This is the same partition characterization as the vendor's verified Itô
formula. Identifying that space integral with a separately constructed
weighted Brownian integral is a further representation theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.VectorItoFormula
open HardSphereDynamics VectorIto VectorQuadraticVariation
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
end SphericalAging.VectorItoFormula
