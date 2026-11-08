module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianNormalizerUnits
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! Actual Gaussian tilted averages of bounded displacement/space observables.
The map is jointly analytic in mass, variance, terminal datum and observable;
the zero-mass branch is the original Gaussian averaging operator. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
end GeneralDepthPaper
