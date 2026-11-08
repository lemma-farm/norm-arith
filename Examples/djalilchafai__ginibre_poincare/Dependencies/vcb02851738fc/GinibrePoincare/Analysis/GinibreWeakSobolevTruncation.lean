module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreSpatialCutoffs
@[expose] public section
/-! # Actual spatial truncation of Ginibre weak-H¹ functions

Smooth compact radial cutoffs converge simultaneously in value and in the
Leibniz gradient. This is a truncation theorem on the independently defined
weak-gradient graph, not a smooth-core density theorem.
-/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
