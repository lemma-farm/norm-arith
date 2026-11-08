module
public import Examples.pmaronow__aging_palomar.Dependencies.v1e3a30d48b13.SphericalAging.PredictableDriftTime
set_option autoImplicit false
public section
/-! Constructive local Picard versions for the full finite-dimensional SDE.
The state space is the actual predictable product L² Banach space and every
stochastic integral uses the complete driving filtration. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.LocalSDE
open HardSphereDynamics PredictableItoTime PredictableDriftTime
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section CoefficientIdentification
variable {X : ℝ≥0 → Ω → State N} {U : PredictableStateL2 N F P} {T : ℝ≥0}
  (hXeq : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun p => X p.1 p.2))
    =ᵐ[nonnegativeLebesgueMeasure.prod P] (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)))
include hXeq
end CoefficientIdentification
end SphericalAging.LocalSDE
