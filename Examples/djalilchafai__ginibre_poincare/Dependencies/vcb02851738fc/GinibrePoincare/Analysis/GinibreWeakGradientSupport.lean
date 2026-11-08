module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
@[expose] public section
/-! # Locality and compact representatives of ordinary weak gradients

The actual weak gradient vanishes almost everywhere outside the topological
support of any value representative. Compact interior values therefore supply
compact interior gradient representatives automatically.
-/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
