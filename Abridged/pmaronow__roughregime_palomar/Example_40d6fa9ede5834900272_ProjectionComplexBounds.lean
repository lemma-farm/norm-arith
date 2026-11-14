module

public import Mathlib

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.ProjectionApproximation ====
public section
@[expose] public section
/-! Concrete source Gram-residual polynomial approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial RealInnerProductSpace
namespace RoughRegime.ProjectionApproximation



def bilinearPolynomial {σ : Type*} {n : ℕ}
    (u : Fin n → MvPolynomial σ ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (v : Fin n → MvPolynomial σ ℝ) : MvPolynomial σ ℝ := u ⬝ᵥ S.mulVec v
end RoughRegime.ProjectionApproximation

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v626bdb740e56.RoughRegime.ComplexDerivativeBridge ====
public section
@[expose] public section
/-! Real derivatives of a real polynomial obey the complex Cauchy bound of Lemma 5(c). -/
noncomputable section
namespace RoughRegime.ComplexDerivativeBridge
def complexify {p : ℕ} (F : MvPolynomial (Fin p) ℝ) : MvPolynomial (Fin p) ℂ :=
  MvPolynomial.map Complex.ofRealHom F
end RoughRegime.ComplexDerivativeBridge

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_40d6fa9ede5834900272_ProjectionComplexBounds ====
@[expose] public section
/-! Degree-independent complex bounds for the concrete bilinear approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionComplex
open  RoughRegime.ProjectionApproximation
open RoughRegime.ComplexDerivativeBridge

set_option linter.unusedVariables false in
lemma bilinearPolynomial_complex_bound {p n : ℕ} (t : Fin p → ℂ)
    (u v : Fin n → MvPolynomial (Fin p) ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ)) (A : ℝ) (hA : 0 ≤ A)
    (hu : ∀ i, ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A)
    (hv : ∀ i, ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A)
    (hS : ∀ i j, ‖MvPolynomial.eval t (complexify (S i j))‖ ≤ A) 
    (h_RoughRegime_ProjectionComplex_bilinearPolynomial_complex_eval : ∀ {p n : ℕ} (t : Fin p → ℂ) (u v : Fin n → MvPolynomial (Fin p) ℝ)
      (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ)),
      (MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
          (RoughRegime.ComplexDerivativeBridge.complexify
            (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v)) =
        ∑ i : Fin n,
          ∑ j : Fin n,
            (MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
                  (RoughRegime.ComplexDerivativeBridge.complexify (u i)) *
                (MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
                  (RoughRegime.ComplexDerivativeBridge.complexify (S i j)) *
              (MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
                (RoughRegime.ComplexDerivativeBridge.complexify (v j)))
    :
    ‖MvPolynomial.eval t (complexify (bilinearPolynomial u S v))‖ ≤ (n : ℝ) ^ 2 * A ^ 3 := by
  rw [h_RoughRegime_ProjectionComplex_bilinearPolynomial_complex_eval]
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
