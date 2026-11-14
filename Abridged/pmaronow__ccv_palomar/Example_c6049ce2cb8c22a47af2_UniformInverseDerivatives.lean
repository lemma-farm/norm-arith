module

public import Mathlib
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_c6049ce2cb8c22a47af2_UniformInverseDerivatives ====
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

/-- The forcing term for Chebyshev polynomials at two possibly noncommuting matrices. -/
def chebyshevForcing (x y : R) (j : ℕ) : R :=
  if j = 0 then y - x else 2 * (y - x) * matrixChebyshevT y j
def chebyshevResponse (x : R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) - 1 - j) * f j

end ChebyshevPerturbation

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]


set_option linter.unusedVariables false in
theorem matrixChebyshevT_norm_volterra (x y : R)
    (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ‖y - x‖ ≤ δ) (n : ℕ) 
    (h_NearlyMinimax_matrixChebyshevU_norm_le : ∀ {R : Type u_1} [inst : NormedRing R] [inst_1 : NormedAlgebra ℝ R] [NormOneClass R] (x : R),
      (∀ (n : ℕ), ‖NearlyMinimax.matrixChebyshevT x n‖ ≤ 1) →
        ∀ (n : ℕ), ‖NearlyMinimax.matrixChebyshevU x (↑n : ℤ)‖ ≤ (↑n : ℝ) + 1)
    (h_NearlyMinimax_matrixChebyshevT_perturbation_identity : ∀ {R : Type u_1} [inst : Ring R] [inst_1 : Algebra ℝ R] (x y : R) (n : ℕ),
      NearlyMinimax.matrixChebyshevT y n - NearlyMinimax.matrixChebyshevT x n =
        NearlyMinimax.chebyshevResponse x (NearlyMinimax.chebyshevForcing x y) n)
    (h_NearlyMinimax_chebyshevForcing_norm_le : ∀ {R : Type u_1} [inst : NormedRing R] [inst_1 : NormedAlgebra ℝ R] [NormOneClass R] (x y : R)
      (δ : ℝ),
      0 ≤ δ →
        ‖y - x‖ ≤ δ →
          ∀ (j : ℕ),
            ‖NearlyMinimax.chebyshevForcing x y j‖ ≤ 2 * δ * ‖NearlyMinimax.matrixChebyshevT y j‖)
    :
    ‖matrixChebyshevT y n‖ ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖ := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖matrixChebyshevU x ((n : ℤ) - 1 - j) * chebyshevForcing x y j‖ ≤
        2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) := by
    have hjn := Finset.mem_range.mp hj
    have hi : (n : ℤ) - 1 - j = ((n - 1 - j : ℕ) : ℤ) := by omega
    have hn : ((n - 1 - j : ℕ) : ℝ) + 1 = ((n - j : ℕ) : ℝ) := by
      exact_mod_cast (show n - 1 - j + 1 = n - j by omega)
    rw [hi]
    calc
      _ ≤ ‖matrixChebyshevU x ((n - 1 - j : ℕ) : ℤ)‖ *
          ‖chebyshevForcing x y j‖ := norm_mul_le _ _
      _ ≤ (((n - 1 - j : ℕ) : ℝ) + 1) *
          (2 * δ * ‖matrixChebyshevT y j‖) :=
        mul_le_mul (h_NearlyMinimax_matrixChebyshevU_norm_le x hx _) (h_NearlyMinimax_chebyshevForcing_norm_le x y δ hδ hd j)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [hn]; ring
  have he : matrixChebyshevT y n = matrixChebyshevT x n +
      chebyshevResponse x (chebyshevForcing x y) n := by
    have h := h_NearlyMinimax_matrixChebyshevT_perturbation_identity x y n
    exact sub_eq_iff_eq_add'.mp h
  rw [he]
  calc
    _ ≤ ‖matrixChebyshevT x n‖ + ‖chebyshevResponse x (chebyshevForcing x y) n‖ := norm_add_le _ _
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        ‖matrixChebyshevU x ((n : ℤ) - 1 - j) * chebyshevForcing x y j‖ :=
      add_le_add (hx n) (norm_sum_le _ _)
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) :=
      add_le_add (le_refl 1) (Finset.sum_le_sum hterm)
    _ = _ := by rw [Finset.mul_sum]

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
