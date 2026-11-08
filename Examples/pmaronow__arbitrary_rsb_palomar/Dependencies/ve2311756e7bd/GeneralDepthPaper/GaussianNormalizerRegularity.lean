module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianVarianceRatio
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! The actual centered Gaussian normalizer is jointly analytic in the mass,
positive variance, and Banach terminal datum, including mass zero. The proof
uses an exact precision change to one fixed Gaussian measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
abbrev ColeHopfParameter := (ℝ×ℝ)×TerminalSpace
end GeneralDepthPaper
