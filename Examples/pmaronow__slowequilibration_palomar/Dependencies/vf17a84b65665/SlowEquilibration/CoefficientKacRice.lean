-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.FunProp
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.DiscreteSubset
set_option autoImplicit false
/-!
# Local coefficient incidence and weighted counting

The gradient is an actual smooth coefficient-linear function. An invertible
coefficient block gives its zero graph by algebra. The weighted equal-dimensional
area formula is applied to the joint incidence map, retaining the full coefficient
and spatial dependence of the Borel weight.
-/
@[expose] public section
namespace SlowEquilibration.CoefficientKacRice
open Set MeasureTheory MeasureTheory.Measure Function Filter
open scoped NNReal ENNReal Topology
noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
def gaussianCoefficientLaw (n m : ℕ) : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))
/-- The actual matching coefficient-space Lebesgue measure. -/
def coefficientVolume (n m : ℕ) : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).prod
    (volume : Measure (EuclideanSpace ℝ (Fin m)))
instance coefficientVolume_isAddHaarMeasure (n m : ℕ) : IsAddHaarMeasure (coefficientVolume n m) :=
  inferInstanceAs (IsAddHaarMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
    (volume : Measure (EuclideanSpace ℝ (Fin m)))))
instance coefficientVolume_sigmaFinite (n m : ℕ) : SigmaFinite (coefficientVolume n m) :=
  inferInstanceAs (SigmaFinite ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod
    (volume : Measure (EuclideanSpace ℝ (Fin m)))))
instance gaussianCoefficientLaw_isProbabilityMeasure (n m : ℕ) : IsProbabilityMeasure (gaussianCoefficientLaw n m) :=
  inferInstanceAs (IsProbabilityMeasure ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))))
end
end SlowEquilibration.CoefficientKacRice
