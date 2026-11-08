module
public import Examples.pmaronow__aging_palomar.Dependencies.v1e3a30d48b13.SphericalAging.HardSphereStochastic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Contracting
set_option autoImplicit false
public section
/-! The genuine Ito Volterra operator on predictable product L².
Its image is obtained from an adapted continuous version and a deterministic
time cut. Product square integrability is proved by Fubini from the actual
fixed-time Ito isometry. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PredictableItoTime
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}
variable {N : ℕ}
end SphericalAging.PredictableItoTime
