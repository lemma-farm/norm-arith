module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Concrete.Configuration
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
/-- Product formula for the Vandermonde determinant. -/
theorem vandermonde_eq_product {n : ℕ} (z : Configuration n) :
    vandermonde z = ∏ i : Fin n, ∏ j > i, (z j - z i) := by
  exact Matrix.det_vandermonde z
theorem vandermonde_permute {n : ℕ} (σ : ParticlePermutation n)
    (z : Configuration n) :
    vandermonde (permute σ z) =
      permutationSign σ * vandermonde z := by
  have hmatrix :
      Matrix.vandermonde (permute σ z) =
        (Matrix.vandermonde z).submatrix σ id := by
    ext i j
    simp [permute]
  unfold vandermonde
  rw [hmatrix]
  simpa [permutationSign] using
    (Matrix.det_permute σ (Matrix.vandermonde z))
end GinibrePoincare
