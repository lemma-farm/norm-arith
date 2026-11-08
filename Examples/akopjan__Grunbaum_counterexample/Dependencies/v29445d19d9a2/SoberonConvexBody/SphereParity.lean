import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.SphereMeasure
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.TensorParity
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.Walsh4
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Integrating finite parity extraction

All averages in this file are literal sums over the sixteen coordinate sign
changes. Their integral preservation follows from sphere measure preservation.
-/
noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 0
instance sphereVolume_finite : IsFiniteMeasure sphereVolume :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure V).toSphere))
end SoberonConvexBody.SphereGeometry
