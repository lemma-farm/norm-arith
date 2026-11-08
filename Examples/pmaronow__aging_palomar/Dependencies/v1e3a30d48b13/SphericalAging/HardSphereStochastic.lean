module
public import Examples.pmaronow__aging_palomar.Dependencies.v1e3a30d48b13.SphericalAging.HardSphereDynamics
public import Examples.pmaronow__aging_palomar.Dependencies.v1e3a30d48b13.FourPapersCommon.FilteredItoL2Continuity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Examples.pmaronow__aging_palomar.Dependencies.v1e3a30d48b13.FourPapersCommon.ContinuousAEAdaptedPredictable
set_option autoImplicit false
public section
/-!
# Finite-driver stochastic integration for the sphere SDE

The driving filtration includes all coordinates. The stochastic operators
below are finite sums of the actual isometrically constructed integrals.
Their continuous versions are proved by the elementary predictable density
and Doob estimates in `FourPapersCommon.FilteredItoContinuous`.
-/
noncomputable section
namespace SphericalAging.HardSphereDynamics
open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal BigOperators ContDiff InnerProductSpace RealInnerProductSpace
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
@[expose] abbrev PredictableStateL2 (N : ℕ) (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) :=
  lpMeas (State N) ℝ F.predictable 2 (nonnegativeLebesgueMeasure.prod P)
end SphericalAging.HardSphereDynamics
