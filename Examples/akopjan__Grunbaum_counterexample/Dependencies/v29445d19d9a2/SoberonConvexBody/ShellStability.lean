import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.ShellBounds
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Quadratic stability of the radial shell

Two independent first-order restrictions occur: the point must lie in the
radial annulus, and its direction must be close to one of four hyperplanes.
The annulus/strip estimate is proved in ShellBounds, not assumed here.
-/
noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators
namespace ShellBounds
open SphereGeometry
end ShellBounds
end SoberonConvexBody
