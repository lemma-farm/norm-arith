module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalOperators
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.AnalyticKernel
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! The genuine centered exponential kernel is analytic in the mass-scaled
terminal datum and positive Gaussian precision, as a bounded function of both
spatial position and Gaussian displacement. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
end GeneralDepthPaper
