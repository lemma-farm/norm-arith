module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v56306555f909.RequestProject.Euler.BanachNonlinearBackwardOrbit
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v56306555f909.RequestProject.Euler.BanachInvariantKernel
/-! The stable space is the actual closed kernel of the bounded
unstable projection. Its power bound is inherited in the original norm. -/
@[expose] public section
set_option maxHeartbeats 1500000
noncomputable section
open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff
namespace Euler2D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
end Euler2D
end
