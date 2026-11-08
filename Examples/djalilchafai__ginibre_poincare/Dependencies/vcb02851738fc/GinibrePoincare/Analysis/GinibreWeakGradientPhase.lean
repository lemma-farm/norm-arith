module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibrePhaseCoordinates
@[expose] public section
/-! # Phase covariance of independently defined ordinary weak gradients

Tests are rotated by actual real-linear, volume-preserving coordinate phases.
The original and rotated collision-free open sets are intersected only for test
separation; no invariance of the Ginibre density under independent phases is used.
-/
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
end
end GinibrePoincare
