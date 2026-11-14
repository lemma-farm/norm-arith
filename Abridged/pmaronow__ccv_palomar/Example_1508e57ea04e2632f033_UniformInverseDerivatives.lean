module

public import Mathlib
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.RoughRegime.Upper ====
public section
@[expose] public section
/-!
Algebraic and analytic ingredients of Section 4.
The declarations explicitly document which paper claims they cover.
-/
noncomputable section
open scoped BigOperators
open Complex
namespace RoughRegime.Upper
def intervalCenter (lo hi : ℝ) : ℝ := (hi + lo) / 2
def intervalHalfWidth (lo hi : ℝ) : ℝ := (hi - lo) / 2

def intervalRho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

open MeasureTheory ProbabilityTheory

end RoughRegime.Upper

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.RoughRegime.MatrixUpper ====
public section
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

end RoughRegime.MatrixUpper

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.RoughRegime.MatrixDeterminant ====
public section
@[expose] public section
/-!
# Determinant coefficients of the matrix reciprocal kernel

The formal determinant series is built from entry polynomials in the actual
matrix variables. Its kth coefficient has total degree at most k.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial
namespace RoughRegime.MatrixDeterminant
open RoughRegime.Upper RoughRegime.MatrixUpper
def kernelCoefficientPolynomial (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  C (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) * normalizedChebyshev lo hi k

end RoughRegime.MatrixDeterminant

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_1508e57ea04e2632f033_UniformInverseDerivatives ====
@[expose] public section
/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]
def matrixChebyshevT (x : R) (n : ℕ) : R := aeval x (Chebyshev.T ℝ (n : ℤ))

end ChebyshevPerturbation
/-- A finite positive weighted geometric constant; it is independent of polynomial degree. -/
def perturbationConstant (η : ℝ) : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * η ^ k

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]

end ChebyshevNorm
section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

end PowerSeriesBounds
section ComplexMatrices
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
def normalizeMatrix (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)


set_option linter.unusedVariables false in
theorem complex_kernel_coefficient_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) 
    (h_NearlyMinimax_normalizedChebyshev_complex_center_bound : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] [Nonempty n] (lo hi : ℝ),
      0 < lo →
        lo < hi →
          ∀ (A : Matrix n n ℂ),
            A.IsHermitian →
              spectrum ℝ A ⊆ Set.Icc lo hi →
                ∀ (k : ℕ),
                  ‖NearlyMinimax.matrixChebyshevT (NearlyMinimax.normalizeMatrix lo hi A) k‖ ≤ 1)
    (h_NearlyMinimax_matrixChebyshevT_neighborhood_bound : ∀ {R : Type u_1} [inst : NormedRing R] [inst_1 : NormedAlgebra ℝ R] [NormOneClass R] (x y : R),
      (∀ (n : ℕ), ‖NearlyMinimax.matrixChebyshevT x n‖ ≤ 1) →
        ∀ (η δ : ℝ),
          0 < η →
            η < 1 →
              0 ≤ δ →
                4 * δ * NearlyMinimax.perturbationConstant η ≤ 1 →
                  ‖y - x‖ ≤ δ → ∀ (n : ℕ), η ^ n * ‖NearlyMinimax.matrixChebyshevT y n‖ ≤ 2)
    (h_NearlyMinimax_normalizedChebyshev_aeval_complex : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] [Nonempty n] (lo hi : ℝ)
      (A : Matrix n n ℂ) (k : ℕ),
      (Polynomial.aeval A : Polynomial ℝ → Matrix n n ℂ)
          (RoughRegime.MatrixUpper.normalizedChebyshev lo hi k) =
        NearlyMinimax.matrixChebyshevT (NearlyMinimax.normalizeMatrix lo hi A) k)
    (h_RoughRegime_Upper_intervalRho_pos : ∀ (lo hi : ℝ), 0 < lo → lo < hi → 0 < RoughRegime.Upper.intervalRho lo hi)
    :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      4 * (intervalRho lo hi / η) ^ k := by
  have hb := h_NearlyMinimax_matrixChebyshevT_neighborhood_bound
    (normalizeMatrix lo hi A) (normalizeMatrix lo hi B)
    (h_NearlyMinimax_normalizedChebyshev_complex_center_bound lo hi hlo hlt A hA hSpec)
    η δ hη hη1 hδ hsmall hd k
  unfold kernelCoefficientPolynomial
  rw [map_mul, aeval_C, ← Algebra.smul_def, norm_smul, h_NearlyMinimax_normalizedChebyshev_aeval_complex]
  have hηk : 0 < η ^ k := pow_pos hη k
  have hr := h_RoughRegime_Upper_intervalRho_pos lo hi hlo hlt
  split_ifs with hk
  · subst k
    simp [matrixChebyshevT]
  · rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num,
      abs_pow, abs_neg, abs_of_pos hr]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hηk).mpr
    calc
      _ = 2 * intervalRho lo hi ^ k * (η ^ k * ‖matrixChebyshevT (normalizeMatrix lo hi B) k‖) := by ring
      _ ≤ 2 * intervalRho lo hi ^ k * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

end ComplexMatrices
section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper  RoughRegime.MatrixDeterminant
variable (r : ℕ) [NeZero r]

end ComplexFreeCoordinates
section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]

end PolynomialBounds
section CoordinateOperators
open scoped Matrix.Norms.L2Operator
variable (r : ℕ) [NeZero r]

open RoughRegime.Upper

end CoordinateOperators
section UniformNeighborhood
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper
variable (r : ℕ) [NeZero r]

end UniformNeighborhood
section ActualDerivatives
end ActualDerivatives
end NearlyMinimax
