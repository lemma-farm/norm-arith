module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.CompactTiltKernel
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalReconstruction
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianNormalizerUnits
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! Normalized compact-tilt responses are actual Gaussian increment averages,
with joint smoothness in all Banach parameters. The proof differentiates the
analytic bounded kernel and uses its genuinely positive uniform normalizer. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
end GeneralDepthPaper
