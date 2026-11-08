module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.UniformBCFTranslation
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.TerminalReconstruction
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! Translation of an actual terminal datum is strongly continuous in its
Banach norm. Highest-jet uniform continuity is exactly the necessary input. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
end GeneralDepthPaper
