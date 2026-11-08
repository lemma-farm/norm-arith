module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v45079d0a1210.RequestProject.Euler.ContourCauchyPole
/-!
# Actual symmetric truncations of the contour Cauchy pole

Every inverse-pole integral used here is over a genuine compact set away
from the origin, and is proved integrable there.  Reflection cancels that
pole on each symmetric truncation.  Dominated convergence is applied only
to the genuinely integrable remainder.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace Euler2D
end Euler2D
