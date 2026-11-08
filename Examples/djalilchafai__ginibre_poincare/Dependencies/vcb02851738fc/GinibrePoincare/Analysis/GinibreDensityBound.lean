module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreDistributionalGradient
public import Mathlib.Analysis.Complex.Exponential
@[expose] public section
/-! # Global boundedness of the actual Ginibre density

A polynomial bound for the Vandermonde square, absorbed by the Gaussian
exponential, yields finite domination by Lebesgue measure.
-/
open MeasureTheory Filter
open scoped BigOperators ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
