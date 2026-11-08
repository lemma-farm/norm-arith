import Mathlib
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.NearIdentity
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.EllipsoidScalar
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.SphereQuadratic
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# A uniform quadratic radial expansion for an affine image of the unit ball

All constants are deliberately coarse. No differentiability of a sign
character, and no regularity hypothesis about cell volumes, is used.
-/
noncomputable section
namespace SoberonConvexBody.Ellipsoid
open scoped BigOperators
open Tensors SphereGeometry NearIdentity
end SoberonConvexBody.Ellipsoid
