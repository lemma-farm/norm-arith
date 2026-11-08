import Mathlib
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.Walsh4
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.Cells
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.Tensors
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v29445d19d9a2.SoberonConvexBody.FrameGeometry
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Geometric and measure-theoretic reduction

Unlike the earlier draft, this file does not package the analytic content in a
single certificate.  Every remaining analytic statement is exposed as a named
lemma with concrete definitions.
-/
noncomputable section
namespace SoberonConvexBody
open Set Real MeasureTheory
open scoped BigOperators
abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev HyperplaneCfg := Cells.HyperplaneCfg
end SoberonConvexBody
