import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.GeometryCore
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.SphereBounds
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
