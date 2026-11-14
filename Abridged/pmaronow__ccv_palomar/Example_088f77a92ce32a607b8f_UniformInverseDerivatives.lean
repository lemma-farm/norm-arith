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

open MeasureTheory ProbabilityTheory

end RoughRegime.Upper

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.RoughRegime.CombinedPolynomial ====
public section
@[expose] public section
/-! The exact entry polynomials for the matrix-inverse/determinant product in
Lemma 5(a), with all matrix entries represented as independent variables. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.CombinedPolynomial
open   Upper
abbrev Variables {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) :=
  (Fin n0 × Fin n0) ⊕ ((i : Fin N) × (Fin (dims i) × Fin (dims i)))

end RoughRegime.CombinedPolynomial

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.NearlyMinimax.PaperInverse ====
public section
@[expose] public section
/-!
# Reciprocal polynomial ingredients for `upper_B.tex`

The imported algebraic and analytic reciprocal construction is specialized to
one parent determinant, exactly the product in the manuscript. Results stated
with Hermitian matrices below explicitly retain that hypothesis. The scalar
exponent bridge identifies the rate parameter with the manuscript's `τ`.
-/
noncomputable section
namespace NearlyMinimax
open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
open RoughRegime.Upper 
open RoughRegime.CombinedPolynomial 
/-- The entry-variable type for the current matrix and its single parent. -/
abbrev parentInverseVariables (r : ℕ) := Variables r (fun _ : Fin 1 => r)


end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Dependencies.vb43d0c79861d.NearlyMinimax.PaperIncrement ====
public section
@[expose] public section
/-! Free-coordinate increment polynomials and their vector-moment structure in Lemma U5(3). -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open MvPolynomial
/-- Current and parent matrix entries together with their regression and density vector moments. -/
abbrev incrementVariables (r : ℕ) := parentInverseVariables r ⊕ (Bool × Bool × Fin r)

open RoughRegime.CombinedPolynomial
open scoped Matrix.Norms.L2Operator
end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_088f77a92ce32a607b8f_UniformInverseDerivatives ====
@[expose] public section
/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]

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
open RoughRegime.Upper  
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
def normalizeMatrix (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)

end ComplexMatrices
section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.CombinedPolynomial 
variable (r : ℕ) [NeZero r]

end ComplexFreeCoordinates
section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]

end PolynomialBounds
section CoordinateOperators
open scoped Matrix.Norms.L2Operator
variable (r : ℕ) [NeZero r]
def currentCoordinateMatrix : (incrementVariables r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z i j := z (Sum.inl (Sum.inl (i, j)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def parentCoordinateMatrix : (incrementVariables r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z i j := z (Sum.inl (Sum.inr ⟨0, (i, j)⟩))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def currentCoordinateCLM : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  (currentCoordinateMatrix r).toContinuousLinearMap
def parentCoordinateCLM : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  (parentCoordinateMatrix r).toContinuousLinearMap

open RoughRegime.Upper
/-- The neighborhood radius is computed from fixed coordinate extraction operators. -/
def inverseCoordinateRadius (lo hi η : ℝ) : ℝ :=
  min 1 ((4 * perturbationConstant η)⁻¹ /
    max 1 (|(intervalHalfWidth lo hi)⁻¹| *
      (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖)))
set_option linter.unusedVariables false in
theorem coordinate_normalized_perturbation (lo hi η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (z z₀ : incrementVariables r → ℂ)
    (hz : ‖z - z₀‖ < inverseCoordinateRadius r lo hi η)
    (F : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (hF : ‖F‖ ≤ ‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖) 
    (h_NearlyMinimax_normalizeMatrix_sub : ∀ {n : Type} [Fintype n] [inst : DecidableEq n] [Nonempty n] (lo hi : ℝ) (A B : Matrix n n ℂ),
      NearlyMinimax.normalizeMatrix lo hi B - NearlyMinimax.normalizeMatrix lo hi A =
        (RoughRegime.Upper.intervalHalfWidth lo hi)⁻¹ • (B - A))
    :
    ‖normalizeMatrix lo hi (F z) - normalizeMatrix lo hi (F z₀)‖ ≤
      (4 * perturbationConstant η)⁻¹ := by
  let D := max 1 (|(intervalHalfWidth lo hi)⁻¹| *
    (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖))
  have hD : 0 < D := (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have hz' : ‖z - z₀‖ ≤ (4 * perturbationConstant η)⁻¹ / D :=
    hz.le.trans (min_le_right _ _)
  rw [h_NearlyMinimax_normalizeMatrix_sub, norm_smul, Real.norm_eq_abs, ← map_sub]
  calc
    _ ≤ |(intervalHalfWidth lo hi)⁻¹| * (‖F‖ * ‖z - z₀‖) :=
      mul_le_mul_of_nonneg_left (F.le_opNorm _) (abs_nonneg _)
    _ ≤ D * ‖z - z₀‖ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (mul_le_mul_of_nonneg_left hF (abs_nonneg _)).trans (le_max_right _ _)
    _ ≤ _ := by simpa only [mul_comm] using (le_div_iff₀ hD).mp hz'
end CoordinateOperators
section UniformNeighborhood
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper
variable (r : ℕ) [NeZero r]

end UniformNeighborhood
section ActualDerivatives
end ActualDerivatives
end NearlyMinimax
