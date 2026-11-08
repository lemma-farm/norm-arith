module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianTiltedSpatial
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalTranslation
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! Actual Gaussian tilted means preserve uniform continuity. The proof uses
strong translation continuity of each terminal datum and each observable, rather
than operator-norm continuity of translations. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
end GeneralDepthPaper
