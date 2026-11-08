module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v363a8b4b3804.GinibrePoincare.Concrete.Configuration
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
@[expose] public section
/-!
# The complex Vandermonde polynomial

This file connects the Vandermonde determinant used in the Ginibre density to
Mathlib's Vandermonde matrix.  It proves the product formula, the precise
collision zero set, nonvanishing on collision-free configurations, and
alternation under particle permutations.
-/
namespace GinibrePoincare
/-- The Vandermonde determinant of a complex particle configuration. -/
def vandermonde {n : ℕ} (z : Configuration n) : ℂ :=
  (Matrix.vandermonde z).det
end GinibrePoincare
