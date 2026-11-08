module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v35e6c87d1055.HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Entrywise matrix contraction

This module defines the entrywise Frobenius contraction used by the
time--velocity operator and relates it to matrix trace when the second matrix
is symmetric.
-/
@[expose] public section
open scoped BigOperators
namespace HypoellipticAleksandrov
/-- The entrywise Frobenius contraction of two real square matrices. -/
def matrixContraction {d : ℕ} (A H : PDE.Mat d) : ℝ :=
  ∑ i, ∑ j, A i j * H i j
end HypoellipticAleksandrov
