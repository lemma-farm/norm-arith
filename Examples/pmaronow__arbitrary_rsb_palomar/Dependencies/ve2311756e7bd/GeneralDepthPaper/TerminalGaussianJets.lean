module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianTiltedOperator
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.GaussianTiltedBounds
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.CenteredColeHopfValue
public import Mathlib
set_option autoImplicit false
@[expose] public section
/-! Banach-valued Gaussian moment polynomials for the first three spatial
Cole–Hopf jets. Their joint analytic regularity uses actual tilted averages;
spatial derivative identification is kept separate from this parameter proof. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
end GeneralDepthPaper
