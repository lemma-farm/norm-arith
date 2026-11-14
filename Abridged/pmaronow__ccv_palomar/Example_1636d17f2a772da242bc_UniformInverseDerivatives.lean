module

public import Mathlib
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_1636d17f2a772da242bc_UniformInverseDerivatives ====
@[expose] public section
/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]
def matrixChebyshevT (x : R) (n : ℕ) : R := aeval x (Chebyshev.T ℝ (n : ℤ))

/-- The forcing term for Chebyshev polynomials at two possibly noncommuting matrices. -/
def chebyshevForcing (x y : R) (j : ℕ) : R :=
  if j = 0 then y - x else 2 * (y - x) * matrixChebyshevT y j

end ChebyshevPerturbation

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]
private axiom norm_two_ring : ‖(2 : R)‖ = 2

theorem chebyshevForcing_norm_le (x y : R) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ‖y - x‖ ≤ δ) (j : ℕ) :
    ‖chebyshevForcing x y j‖ ≤ 2 * δ * ‖matrixChebyshevT y j‖ := by
  unfold chebyshevForcing
  split_ifs with hj
  · subst j
    simpa [matrixChebyshevT] using hd.trans (show δ ≤ 2 * δ by linarith)
  · calc
      _ ≤ ‖(2 : R) * (y - x)‖ * ‖matrixChebyshevT y j‖ := norm_mul_le _ _
      _ ≤ (2 * δ) * ‖matrixChebyshevT y j‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_mul_le _ _).trans (by rw [norm_two_ring]; gcongr)

end ChebyshevNorm
section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

end PowerSeriesBounds
section ComplexMatrices
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

end ComplexMatrices
section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator

variable (r : ℕ) [NeZero r]

end ComplexFreeCoordinates
section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]

end PolynomialBounds
section CoordinateOperators
open scoped Matrix.Norms.L2Operator
variable (r : ℕ) [NeZero r]



end CoordinateOperators
section UniformNeighborhood
open scoped Matrix.Norms.L2Operator

variable (r : ℕ) [NeZero r]

end UniformNeighborhood
section ActualDerivatives
end ActualDerivatives
end NearlyMinimax
