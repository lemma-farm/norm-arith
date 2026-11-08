import Examples.akopjan__Grunbaum_counterexample.Dependencies.v08df8568ab54.SoberonConvexBody.TensorZeroAlgebra
import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# Local elimination of tensor zeros

This module proves local nonvanishing by exact polynomial elimination and
quadratic inequalities. No differentiability theorem or local inverse theorem
is needed. The neighborhood is a concrete open semialgebraic set of frames.
-/
noncomputable section
namespace SoberonConvexBody.Tensors
open Set
/-- Standard coordinate vector. -/
def coordinateVector (i : Fin 4) : E4 :=
  EuclideanSpace.single i 1
@[simp] theorem coordinateVector_apply (i j : Fin 4) :
    coordinateVector i j = if j = i then (1 : Real) else 0 := by
  simp [coordinateVector, PiLp.single_apply, eq_comm]
end SoberonConvexBody.Tensors
