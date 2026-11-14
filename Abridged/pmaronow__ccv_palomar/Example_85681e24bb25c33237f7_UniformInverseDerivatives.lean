module

public import Mathlib
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_85681e24bb25c33237f7_UniformInverseDerivatives ====
@[expose] public section
/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]
def matrixChebyshevT (x : R) (n : ℕ) : R := aeval x (Chebyshev.T ℝ (n : ℤ))
def matrixChebyshevU (x : R) (n : ℤ) : R := aeval x (Chebyshev.U ℝ n)

end ChebyshevPerturbation

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]
private axiom norm_two_ring : ‖(2 : R)‖ = 2
theorem matrixChebyshevU_norm_le (x : R) (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (n : ℕ) :
    ‖matrixChebyshevU x (n : ℤ)‖ ≤ (n : ℝ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevU]
  | one =>
    have hx1 : ‖x‖ ≤ 1 := by simpa [matrixChebyshevT] using hx 1
    simp only [matrixChebyshevU, Nat.cast_one, Chebyshev.U_one, map_mul, map_ofNat, aeval_X]
    calc
      _ ≤ ‖(2 : R)‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ 2 := by rw [norm_two_ring]; linarith
      _ = _ := by norm_num
  | more n hn hn1 =>
    have he : matrixChebyshevU x ((n + 2 : ℕ) : ℤ) =
        2 * matrixChebyshevT x (n + 2) + matrixChebyshevU x (n : ℤ) := by
      unfold matrixChebyshevU matrixChebyshevT
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega, Chebyshev.U_eq_two_mul_T_add_U]
      simp [map_ofNat]
    rw [he]
    calc
      _ ≤ ‖2 * matrixChebyshevT x (n + 2)‖ + ‖matrixChebyshevU x (n : ℤ)‖ := norm_add_le _ _
      _ ≤ 2 * ‖matrixChebyshevT x (n + 2)‖ + ((n : ℝ) + 1) := by
        exact add_le_add (by simpa only [norm_two_ring] using norm_mul_le (2 : R) _) hn
      _ ≤ _ := by have h := hx (n + 2); push_cast; linarith

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
