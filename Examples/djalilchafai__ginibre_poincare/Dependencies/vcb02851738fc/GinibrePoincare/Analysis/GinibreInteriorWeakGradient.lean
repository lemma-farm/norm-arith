module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreLocalSobolev
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.SobolevTruncation
@[expose] public section
/-! # Interior compact weak-gradient pairs and ordinary mollification

The ordinary local Ginibre weak derivative identity extends to all Lebesgue
tests when both representatives have compact support away from collisions.
This allows genuine smooth convolution of those representatives.
-/
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
