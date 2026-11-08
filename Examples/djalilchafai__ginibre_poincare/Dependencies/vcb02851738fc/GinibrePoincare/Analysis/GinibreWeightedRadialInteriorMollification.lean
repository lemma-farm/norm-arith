module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreRadialInteriorMollification
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.GinibreLebesgueL2Transfer
@[expose] public section
/-! # Actual weighted value-and-gradient convergence of interior mollification

The density bound transfers the simultaneous ordinary L² convergence to the
actual Ginibre L² graph topology. The smooth functions are concrete normalized
bump convolutions, and their gradients are their actual classical gradients.
-/
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
