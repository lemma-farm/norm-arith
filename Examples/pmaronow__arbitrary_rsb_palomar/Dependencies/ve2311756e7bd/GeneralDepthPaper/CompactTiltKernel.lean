module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalKernel
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.ParametricGaussianAverage
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! An analytic kernel uniform in a compact auxiliary tilt. An independent
second terminal direction allows differentiation of its normalizer without
introducing a division by the auxiliary tilt at zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
end GeneralDepthPaper
