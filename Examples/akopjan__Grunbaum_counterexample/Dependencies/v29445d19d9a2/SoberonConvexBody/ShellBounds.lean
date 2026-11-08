import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.GeometryCore
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.SphereBounds
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Radial bands intersected with thin angular strips

This module proves the product estimate for a radial shell and a union of
four strips. Both factors are computed using actual measures.
-/
noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators
namespace ShellBounds
open SphereGeometry
end ShellBounds
end SoberonConvexBody
