module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreWeakGradient
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.SobolevTruncation
@[expose] public section
/-! # Smooth symmetric radial spatial cutoffs

Cutoffs of the total squared radius are smooth in the original configuration
coordinates. Their squared gradient is uniformly O(1/(m+1)).
-/
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
