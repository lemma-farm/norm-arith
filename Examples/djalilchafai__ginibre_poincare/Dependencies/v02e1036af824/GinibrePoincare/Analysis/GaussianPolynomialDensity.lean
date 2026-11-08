module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Analysis.MultivariateHermiteIntegrability
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
@[expose] public section
/-! # Polynomial subspaces in Gaussian `L²`

This module packages the multivariate complex Hermite polynomials as actual
vectors of Gaussian `L²`, and records the unconditional analytic density
input supplied by weak regularity: bounded continuous functions are dense in
that space.  This is the natural first reduction in the proof that the
Hermite polynomial span is dense.
-/
open MeasureTheory
open Filter
open scoped ENNReal
namespace GinibrePoincare
noncomputable section
open ComplexHermite
end
end GinibrePoincare
