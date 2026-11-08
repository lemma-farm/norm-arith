module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianNormalizerRegularity
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.ColeHopfMassRegularity
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! A genuine uniform lower bound for the centered normalizer. It makes the
normalizer a unit of the bounded-function Banach algebra, so normalization is
an analytic operation, including at zero mass. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
open ColeHopfFoundation.ProbabilityTheory
end GeneralDepthPaper
