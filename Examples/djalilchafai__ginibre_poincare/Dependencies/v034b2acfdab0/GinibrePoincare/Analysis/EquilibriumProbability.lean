module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v034b2acfdab0.GinibrePoincare.Analysis.EquilibriumFactorization
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Probability.Independence.Basic
@[expose] public section
/-!
# Probabilistic equilibrium factorization

The actual joint law of the coordinate sum `S` and zero-sum component `W`
is the product of the standard complex Gaussian and the recentered Ginibre
marginal. Haar uniqueness supplies the positive constant Jacobian; the
pointwise density identity supplies the product density. The recentered
marginal's normalization follows from the already proved Ginibre probability
normalization. The Gamma law of `n |W|²` is not part of this module.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace GinibrePoincare
noncomputable section
/-- The standard complex Gaussian, with density `π⁻¹ exp (-|s|²)`. -/
def standardComplexGaussianMeasure : Measure ℂ :=
  complexCoordinateGaussianProbability 1
instance : IsProbabilityMeasure standardComplexGaussianMeasure := by
  unfold standardComplexGaussianMeasure
  infer_instance
def recenteredVolume (n : ℕ) : Measure (zeroSumHyperplane n) := Measure.addHaar
instance (n : ℕ) : Measure.IsAddHaarMeasure (recenteredVolume n) := by
  unfold recenteredVolume
  infer_instance
instance (n : ℕ) : SigmaFinite (recenteredVolume n) := by
  unfold recenteredVolume
  infer_instance
end
end GinibrePoincare
