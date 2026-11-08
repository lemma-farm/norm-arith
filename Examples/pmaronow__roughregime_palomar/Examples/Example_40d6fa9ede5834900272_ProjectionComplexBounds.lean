module
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.ProjectionComplex
public import Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.ComplexGram
public import Mathlib
@[expose] public section
/-! Degree-independent complex bounds for the concrete bilinear approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionComplex
open RoughRegime.KernelExpressions RoughRegime.ProjectionApproximation
open RoughRegime.ComplexDerivativeBridge
lemma bilinearPolynomial_complex_eval {p n : ℕ} (t : Fin p → ℂ)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ)) :
    MvPolynomial.eval t (complexify (bilinearPolynomial u S v)) =
      ∑ i : Fin n, ∑ j : Fin n,
        MvPolynomial.eval t (complexify (u i)) *
          MvPolynomial.eval t (complexify (S i j)) *
          MvPolynomial.eval t (complexify (v j)) := by
  simp only [← complexEvaluation_eq, bilinearPolynomial, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.mul_sum, mul_assoc]
lemma bilinearPolynomial_complex_bound {p n : ℕ} (t : Fin p → ℂ)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ)) (A : ℝ) (hA : 0 ≤ A)
    (hu : ∀ i, ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A)
    (hv : ∀ i, ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A)
    (hS : ∀ i j, ‖MvPolynomial.eval t (complexify (S i j))‖ ≤ A) :
    ‖MvPolynomial.eval t (complexify (bilinearPolynomial u S v))‖ ≤ (n : ℝ) ^ 2 * A ^ 3 := by
  rw [bilinearPolynomial_complex_eval]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
      ‖MvPolynomial.eval t (complexify (u i))‖ *
        ‖MvPolynomial.eval t (complexify (S i j))‖ *
        ‖MvPolynomial.eval t (complexify (v j))‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul] using (norm_sum_le Finset.univ
        (fun j : Fin n => MvPolynomial.eval t (complexify (u i)) *
          MvPolynomial.eval t (complexify (S i j)) * MvPolynomial.eval t (complexify (v j))))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, A * A * A := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (mul_le_mul (hu i) (hS i j) (norm_nonneg _) hA)
        (hv j) (norm_nonneg _) (mul_nonneg hA hA)
    _ = _ := by simp; ring
end RoughRegime.ProjectionComplex
