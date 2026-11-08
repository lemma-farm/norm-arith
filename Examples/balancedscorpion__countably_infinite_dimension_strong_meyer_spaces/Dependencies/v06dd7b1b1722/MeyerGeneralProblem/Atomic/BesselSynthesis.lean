module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Atomic.SupportSubspace
public import Mathlib
import all Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Extend
import all Mathlib.Analysis.Normed.Operator.Extend
@[expose] public section
/-!
# Bessel-family analysis and synthesis

This module packages the analytic content of a Bessel estimate as a continuous
analysis operator into the canonical coefficient space. Its Hilbert adjoint is
then the genuine infinite synthesis operator. The construction records the
coordinate formula, its action on basis atoms, and convergence of the
coefficient series; no summability assertion is hidden in a formal sum.
-/
namespace MeyerGeneralProblem
noncomputable section
open scoped lp
variable {ι H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- Bundled Bessel data for a Hilbert-space family. The continuous analysis
map records precisely the analytic square-summability estimate; its `i`th
coordinate is the inner product against the `i`th family vector. -/
structure BesselAnalysis (v : ι → H) where
  /-- The bounded analysis operator into `ℓ²(ι, ℂ)`. -/
  toContinuousLinearMap : H →L[ℂ] CoefficientSpace ι
  /-- Coordinate identification of the analysis operator. -/
  coefficient : ∀ x i, toContinuousLinearMap x i = inner ℂ (v i) x
namespace BesselAnalysis
variable {v : ι → H}
end BesselAnalysis
end
end MeyerGeneralProblem
