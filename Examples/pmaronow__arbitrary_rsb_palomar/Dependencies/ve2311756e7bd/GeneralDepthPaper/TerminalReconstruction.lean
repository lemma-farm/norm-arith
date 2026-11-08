module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalOperators
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! Reconstruction identifies the compatible Banach jets with the actual C³
terminal functions, and the inherited norm is equivalent to the sum norm in
Appendix A. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
end GeneralDepthPaper
