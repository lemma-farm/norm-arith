import Mathlib
import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.Walsh4
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Sign cells and the finite Walsh criterion

This module separates the combinatorial meaning of the fifteen Walsh equations
from all geometry.  A boundary point is assigned to the positive side of each
oriented hyperplane, so the sixteen sign cells are literally disjoint and cover
all of space; no null-boundary hypothesis is needed for the partition itself.
-/
noncomputable section
namespace SoberonConvexBody
namespace Cells
open Set MeasureTheory
open scoped BigOperators
abbrev E4 := EuclideanSpace ℝ (Fin 4)
structure HyperplaneCfg where
  normal : Fin 4 → E4
  offset : Fin 4 → ℝ
/-- Boolean sign pattern. `true` means the closed positive side. -/
def pattern (c : HyperplaneCfg) (x : E4) : Walsh4.Pattern :=
  fun i => decide (¬ inner ℝ x (c.normal i) < c.offset i)
def signCharacter (c : HyperplaneCfg) (I : Walsh4.Index) (x : E4) : ℝ :=
  Walsh4.char I (pattern c x)
end Cells
end SoberonConvexBody
