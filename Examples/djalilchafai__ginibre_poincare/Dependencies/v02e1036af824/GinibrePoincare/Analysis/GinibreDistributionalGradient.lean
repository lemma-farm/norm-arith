module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Analysis.GinibreWeakGradient
@[expose] public section
/-! # Ordinary distributional gradients on the collision-free open set

Weighted L² values and gradients are locally Lebesgue integrable where the
Ginibre density is positive. The density-weighted weak identities imply the
usual distributional derivative identity against every smooth test compactly
supported in this open set. No reverse smooth-core approximation is assumed.
-/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 300000
end
end GinibrePoincare
