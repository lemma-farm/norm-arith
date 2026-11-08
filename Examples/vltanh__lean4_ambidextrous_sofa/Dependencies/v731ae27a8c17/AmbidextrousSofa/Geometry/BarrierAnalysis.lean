module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Geometry.Barriers
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Finite, measurable, and integrable whole-angle barriers

The two individual wall heights can have small denominators near an endpoint
of the angular interval. Their minimum nevertheless has a uniform upper
bound: on the first quadrant at least one of sine and cosine is at least
one half. That wall alone controls the minimum. Compactness of the actual
set supplies a common support bound on the closed quarter-turn.

Consequently the real supremum in `sweptNiche` is a genuine bounded supremum,
at every horizontal coordinate, including outside the body's projection.
It is lower semicontinuous as a supremum of continuous wall minima. The
terminal wall is retained in `partialBarrier`; both barriers are measurable
and integrable on every compact horizontal interval.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
/-! ## Continuous affine walls -/
end AmbidextrousSofa
