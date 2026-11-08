module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Concrete.Configuration
public import Mathlib
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
