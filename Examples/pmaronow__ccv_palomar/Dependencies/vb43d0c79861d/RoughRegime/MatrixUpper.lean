module
public import Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.RoughRegime.Upper
@[expose] public section
/-!
Matrix spectral ingredients and the inverse-only (`N = 0`) specialization of Lemma 5(a).
The determinant-product case of that lemma is deliberately not claimed here.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial RoughRegime.Upper
namespace RoughRegime.MatrixUpper
/-- The `k`th normalized Chebyshev polynomial on the positive interval. -/
def normalizedChebyshev (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
    (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi)))
lemma normalizedChebyshev_eval (lo hi x : ℝ) (k : ℕ) :
    (normalizedChebyshev lo hi k).eval x =
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) := by
  simp [normalizedChebyshev, div_eq_mul_inv, mul_comm]
def variableMatrix (n : Type*) : Matrix n n (MvPolynomial (n × n) ℝ) :=
  fun i j => MvPolynomial.X (i, j)
def matrixEntryPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : MvPolynomial (n × n) ℝ :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    MvPolynomial.C (q.coeff k) * (variableMatrix n ^ k) i j
end RoughRegime.MatrixUpper
