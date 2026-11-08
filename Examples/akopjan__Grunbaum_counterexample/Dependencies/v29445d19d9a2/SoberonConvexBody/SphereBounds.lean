import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.SphereMeasure
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.FrameBasics
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Explicit thin-strip estimates on the four-dimensional unit sphere

The proof uses only the cone definition of `volume.toSphere`, the measure
of a rectangular box, and orthogonal invariance. There is no assumed
surface-area or coarea formula in this module.
-/
noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped Pointwise BigOperators
end SoberonConvexBody.SphereGeometry
