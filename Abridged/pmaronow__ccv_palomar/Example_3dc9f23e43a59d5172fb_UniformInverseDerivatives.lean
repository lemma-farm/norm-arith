module

public import Mathlib
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_3dc9f23e43a59d5172fb_UniformInverseDerivatives ====
@[expose] public section
/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]

end ChebyshevPerturbation

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]

end ChebyshevNorm
section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

end PowerSeriesBounds
section ComplexMatrices
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]


theorem matrix_entry_norm_le_l2 (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
  have hi := PiLp.norm_apply_le (T e) i
  have hentry : (T e) i = A i j := by
    simp [T, e, Matrix.toEuclideanCLM_toLp, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  rw [hentry] at hi
  exact hi.trans (by simpa [he, T, Matrix.l2_opNorm_toEuclideanCLM] using
    (T.le_opNorm e))

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
