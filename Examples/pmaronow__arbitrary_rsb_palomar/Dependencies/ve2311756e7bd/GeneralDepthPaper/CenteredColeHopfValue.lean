module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.CompactTiltResponse
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.UnitTiltAverage
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianVarianceRatio
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.ColeHopfCentered
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! The actual centered Cole–Hopf value is jointly C∞ as a bounded spatial
function, including at mass zero. The auxiliary-tilt response supplies its
removable extension and the exact Gaussian precision identity handles variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory
end GeneralDepthPaper
