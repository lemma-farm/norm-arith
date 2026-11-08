module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.GaussianProbability
public import Mathlib.Probability.Distributions.Gaussian.Real
@[expose] public section
/-!
# Density of the real coordinates of the Ginibre Gaussian

This file begins the identification of the probability measure constructed in
`Concrete.GaussianProbability` with an explicit Lebesgue density.  The first
step is completely supplied by Mathlib's density theorem for a nondegenerate
real Gaussian; the only point specific to the Ginibre normalization is proving
that the variance `1 / (2n)` is nonzero when `n > 0`.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
end
end GinibrePoincare
