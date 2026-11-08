import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.SphereParity
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Degree at most two under the coordinate sign characters

All selection rules are proved by averaging the sixteen coordinate reflections.
No numerical evaluation of a spherical moment is needed.
-/
noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped BigOperators
set_option maxRecDepth 200000
set_option maxHeartbeats 0
end SoberonConvexBody.SphereGeometry
