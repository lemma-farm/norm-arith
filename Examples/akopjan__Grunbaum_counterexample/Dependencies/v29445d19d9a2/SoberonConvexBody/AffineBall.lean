import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.EllipsoidExpansion
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.PolarGeneral
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Walsh integrals after straightening four affine hyperplanes

The affine map changes the body, not the signs. The transformed ball has the
explicit positive quadratic root developed in `EllipsoidExpansion`.
-/
noncomputable section
namespace SoberonConvexBody.Ellipsoid
open Set MeasureTheory
open scoped BigOperators
open Tensors SphereGeometry NearIdentity
def errorMatrix (e : E4 ≃ₗ[Real] E4) (i j : Fin 4) : Real :=
  e (coordinateVector j) i - if i=j then 1 else 0
end SoberonConvexBody.Ellipsoid
