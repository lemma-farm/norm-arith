import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.TensorDefs
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Rotations and null coordinate sections of the unit sphere

The normalization is mathlib's `volume.toSphere`. Its cone formula is used
directly, so no separate surface measure is postulated.
-/
noncomputable section
namespace SoberonConvexBody.SphereGeometry
open Set MeasureTheory
open scoped Pointwise BigOperators
abbrev V := Tensors.E4
abbrev UnitSphere := ↥(Metric.sphere (0 : V) 1)
def sphereVolume : Measure UnitSphere := (volume : Measure V).toSphere
end SoberonConvexBody.SphereGeometry
