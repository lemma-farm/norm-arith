module
public import Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v56306555f909.RequestProject.Euler.BanachNonlinearKernelOrbit
/-! Uniqueness for the actual exponentially weighted backward equation.
The Green identity is recovered from its proved recurrence and the original
complement power bound, rather than assumed as an inverse property. -/
@[expose] public section
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology Metric
open scoped BoundedContinuousFunction ContDiff
namespace Euler2D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
end Euler2D
end
