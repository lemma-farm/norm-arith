module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.LebesgueL2Mollification
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
@[expose] public section
/-! # Concrete smooth compact convolution in ordinary L²

For compactly supported L² representatives, the actual normalized bump
convolution represents the Bochner L² average. Consequently the concrete
smooth compact functions converge strongly in L² as the bump radius shrinks.
-/
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
end
end GinibrePoincare
