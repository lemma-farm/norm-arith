module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.RadialGaussianOrthogonality
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreSpatialCutoffs
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
@[expose] public section
/-! # Radial and symmetric convolution under Lebesgue measure

Independent coordinate phases preserve Lebesgue measure. Radial kernels and
radial values therefore have radial convolutions; permutation invariance is
preserved as well. Concrete spatial-radius cutoffs provide such kernels.
-/
open MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
