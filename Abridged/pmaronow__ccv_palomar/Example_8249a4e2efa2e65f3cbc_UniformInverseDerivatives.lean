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
def intervalGeometricMean (lo hi : ℝ) : ℝ := Real.sqrt (lo * hi)
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

def variableMatrix (n : Type*) : Matrix n n (MvPolynomial (n × n) ℝ) :=
  fun i j => MvPolynomial.X (i, j)
def matrixEntryPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : MvPolynomial (n × n) ℝ :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    MvPolynomial.C (q.coeff k) * (variableMatrix n ^ k) i j
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
def variableKernelSeries (lo hi : ℝ) {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix n n (PowerSeries (MvPolynomial (n × n) ℝ)) := fun i j =>
  PowerSeries.mk (fun k => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j)
end RoughRegime.MatrixDeterminant

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
open MatrixDeterminant MatrixUpper Upper
abbrev Variables {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) :=
  (Fin n0 × Fin n0) ⊕ ((i : Fin N) × (Fin (dims i) × Fin (dims i)))
def inverseVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin n0 × Fin n0 => (Sum.inl ab : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi a b)
def determinantVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (i : Fin N) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  PowerSeries.map (MvPolynomial.rename
    (fun ab : Fin (dims i) × Fin (dims i) => (Sum.inr ⟨i, ab⟩ : Variables n0 dims))).toRingHom
    (variableKernelSeries lo hi (n := Fin (dims i))).det
def combinedVariableSeries {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) : PowerSeries (MvPolynomial (Variables n0 dims) ℝ) :=
  inverseVariableSeries n0 dims lo hi a b * ∏ i, determinantVariableSeries n0 dims lo hi i
def combinedCoefficientPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (k : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  PowerSeries.coeff k (combinedVariableSeries n0 dims lo hi a b)
def truncationEntryPolynomial {N : ℕ} (n0 : ℕ) (dims : Fin N → ℕ) (lo hi : ℝ)
    (a b : Fin n0) (m : ℕ) : MvPolynomial (Variables n0 dims) ℝ :=
  MvPolynomial.C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹) *
    ∑ k ∈ Finset.range (m + 1), combinedCoefficientPolynomial n0 dims lo hi a b k
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
open RoughRegime.Upper RoughRegime.MatrixUpper
open RoughRegime.CombinedPolynomial 
/-- The entry-variable type for the current matrix and its single parent. -/
abbrev parentInverseVariables (r : ℕ) := Variables r (fun _ : Fin 1 => r)
/-- Exact free-entry polynomial implementing the manuscript's single-parent truncation. -/
def parentInverseEntryPolynomial (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    MvPolynomial (parentInverseVariables r) ℝ :=
  truncationEntryPolynomial r (fun _ : Fin 1 => r) a b i j m
open RoughRegime.MatrixDeterminant
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
def currentVariableMatrix (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inl (i, j))
def parentVariableMatrix (r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (parentInverseVariables r) ℝ) :=
  fun i j => X (Sum.inr ⟨0, (i, j)⟩)
def vectorMoment (r : ℕ) (parent response : Bool) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ := X (Sum.inr (parent, response, i))
def rawNumeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  rename Sum.inl (parentVariableMatrix r).det * vectorMoment r false response i -
    ∑ j, ∑ k, ∑ l,
      rename Sum.inl (currentVariableMatrix r i j) * C (T j k) *
      rename Sum.inl ((parentVariableMatrix r).adjugate k l) * vectorMoment r true response l
/-- The exact determinant-cleared numerator, affine in the formal response `y`. -/
def numeratorPolynomial (r : ℕ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (i : Fin r) :
    MvPolynomial (incrementVariables r) ℝ :=
  rawNumeratorPolynomial r T false i - C y * rawNumeratorPolynomial r T true i
def incrementEntryPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) : MvPolynomial (incrementVariables r) ℝ :=
  ∑ j, rename Sum.inl (parentInverseEntryPolynomial a b r m i j) * numeratorPolynomial r T y j
open RoughRegime.CombinedPolynomial
open scoped Matrix.Norms.L2Operator
end NearlyMinimax

end
end
end

-- ==== Examples.pmaronow__ccv_palomar.Examples.Example_8249a4e2efa2e65f3cbc_UniformInverseDerivatives ====
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
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
def normalizeMatrix (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)

/-- The complex kernel is evaluated at arbitrary, possibly nonnormal matrices. -/
def complexKernelSeries (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun k => (aeval A (kernelCoefficientPolynomial lo hi k)) i j)

end ComplexMatrices
section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.CombinedPolynomial RoughRegime.MatrixDeterminant
variable (r : ℕ) [NeZero r]
def complexParentValuation (A C : Matrix (Fin r) (Fin r) ℂ) : parentInverseVariables r → ℂ
  | Sum.inl ij => A ij.1 ij.2
  | Sum.inr ⟨_, ij⟩ => C ij.1 ij.2

end ComplexFreeCoordinates
section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A concrete finite coefficient envelope for a real polynomial on a complex coordinate ball. -/
def polynomialCoordinateBound (P : MvPolynomial V ℝ) (R : ℝ) : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖ * ∏ j : V, R ^ α j

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

end CoordinateOperators
section UniformNeighborhood
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper
variable (r : ℕ) [NeZero r]
def inverseComplexEnvelope (lo hi q : ℝ) : ℝ :=
  |(intervalGeometricMean lo hi ^ (r + 1))⁻¹| *
    ((Fintype.card (Equiv.Perm (Fin r)) : ℝ) * 4 ^ (r + 1)) *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (r + 1) * q ^ k
def incrementComplexEnvelope (lo hi q L : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) : ℝ :=
  inverseComplexEnvelope r lo hi q *
    ∑ j : Fin r, polynomialCoordinateBound (numeratorPolynomial r T y j) (L + 1)

set_option linter.unusedVariables false in
theorem actual_increment_complex_neighborhood (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (η : ℝ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (L : ℝ) (hL : 0 ≤ L) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ)
    (z₀ z : incrementVariables r → ℂ) (hz₀ : ‖z₀‖ ≤ L)
    (hA : (currentCoordinateCLM r z₀).IsHermitian)
    (hC : (parentCoordinateCLM r z₀).IsHermitian)
    (hASpec : spectrum ℝ (currentCoordinateCLM r z₀) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (parentCoordinateCLM r z₀) ⊆ Set.Icc lo hi)
    (hz : ‖z - z₀‖ < inverseCoordinateRadius r lo hi η) (m : ℕ) (i : Fin r) 
    (h_NearlyMinimax_coordinate_normalized_perturbation : ∀ (r : ℕ) [NeZero r] (lo hi η : ℝ),
      0 < η →
        η < 1 →
          ∀ (z z₀ : NearlyMinimax.incrementVariables r → ℂ),
            ‖z - z₀‖ < NearlyMinimax.inverseCoordinateRadius r lo hi η →
              ∀ (F : (NearlyMinimax.incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ),
                ‖F‖ ≤ ‖NearlyMinimax.currentCoordinateCLM r‖ + ‖NearlyMinimax.parentCoordinateCLM r‖ →
                  ‖NearlyMinimax.normalizeMatrix lo hi
                          ((F : (NearlyMinimax.incrementVariables r → ℂ) → Matrix (Fin r) (Fin r) ℂ)
                            z) -
                        NearlyMinimax.normalizeMatrix lo hi
                          ((F : (NearlyMinimax.incrementVariables r → ℂ) → Matrix (Fin r) (Fin r) ℂ)
                            z₀)‖ ≤
                    (4 * NearlyMinimax.perturbationConstant η)⁻¹)
    (h_NearlyMinimax_inverseComplexEnvelope_nonneg : ∀ (r : ℕ) [NeZero r] (lo hi q : ℝ), 0 ≤ q → 0 ≤ NearlyMinimax.inverseComplexEnvelope r lo hi q)
    (h_NearlyMinimax_polynomial_complex_coordinate_bound : ∀ {V : Type} [inst : Fintype V] [DecidableEq V] (P : MvPolynomial V ℝ) (z : V → ℂ) (R : ℝ),
      0 ≤ R →
        (∀ (j : V), ‖z j‖ ≤ R) →
          ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ NearlyMinimax.polynomialCoordinateBound P R)
    (h_NearlyMinimax_perturbationConstant_pos : ∀ (η : ℝ), 0 < η → η < 1 → 0 < NearlyMinimax.perturbationConstant η)
    (h_NearlyMinimax_coordinate_parent_valuation : ∀ (r : ℕ) [NeZero r] (z : NearlyMinimax.incrementVariables r → ℂ),
      z ∘ Sum.inl =
        NearlyMinimax.complexParentValuation r
          ((NearlyMinimax.currentCoordinateCLM r :
              (NearlyMinimax.incrementVariables r → ℂ) → Matrix (Fin r) (Fin r) ℂ)
            z)
          ((NearlyMinimax.parentCoordinateCLM r :
              (NearlyMinimax.incrementVariables r → ℂ) → Matrix (Fin r) (Fin r) ℂ)
            z))
    (h_NearlyMinimax_parentInverseEntryPolynomial_eval_complex : ∀ (r : ℕ) [NeZero r] (lo hi : ℝ) (A C : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (m : ℕ),
      MvPolynomial.eval₂ Complex.ofRealHom (NearlyMinimax.complexParentValuation r A C)
          (NearlyMinimax.parentInverseEntryPolynomial lo hi r m i j) =
        (↑(RoughRegime.Upper.intervalGeometricMean lo hi ^ (r + 1))⁻¹ : ℂ) *
          ∑ k ∈ Finset.range (m + 1),
            (PowerSeries.coeff k : PowerSeries ℂ → ℂ)
              (NearlyMinimax.complexKernelSeries lo hi A i j *
                (NearlyMinimax.complexKernelSeries lo hi C).det))
    (h_NearlyMinimax_complex_kernel_entry_coefficient_bound : ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [Nonempty n] (lo hi : ℝ),
      0 < lo →
        lo < hi →
          ∀ (A B : Matrix n n ℂ),
            A.IsHermitian →
              spectrum ℝ A ⊆ Set.Icc lo hi →
                ∀ (η δ : ℝ),
                  0 < η →
                    η < 1 →
                      0 ≤ δ →
                        4 * δ * NearlyMinimax.perturbationConstant η ≤ 1 →
                          ‖NearlyMinimax.normalizeMatrix lo hi B -
                                  NearlyMinimax.normalizeMatrix lo hi A‖ ≤
                              δ →
                            ∀ (i j : n) (k : ℕ),
                              ‖(PowerSeries.coeff k : PowerSeries ℂ → ℂ)
                                    (NearlyMinimax.complexKernelSeries lo hi B i j)‖ ≤
                                4 * (RoughRegime.Upper.intervalRho lo hi / η) ^ k)
    (h_NearlyMinimax_combined_truncation_uniform_bound : ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [Nonempty n]
      (K L : Matrix n n (PowerSeries ℂ)) (q B : ℝ),
      0 < q →
        q < 1 →
          0 ≤ B →
            (∀ (i j : n) (k : ℕ), ‖(PowerSeries.coeff k : PowerSeries ℂ → ℂ) (K i j)‖ ≤ B * q ^ k) →
              (∀ (i j : n) (k : ℕ), ‖(PowerSeries.coeff k : PowerSeries ℂ → ℂ) (L i j)‖ ≤ B * q ^ k) →
                ∀ (i j : n) (m : ℕ),
                  ‖∑ k ∈ Finset.range (m + 1),
                        (PowerSeries.coeff k : PowerSeries ℂ → ℂ) (K i j * L.det)‖ ≤
                    (↑(Fintype.card (Equiv.Perm n)) : ℝ) * B ^ (Fintype.card n + 1) *
                      ∑' (k : ℕ), (↑(k + 1) : ℝ) ^ (Fintype.card n + 1) * q ^ k)
    (h_RoughRegime_Upper_intervalRho_pos : ∀ (lo hi : ℝ), 0 < lo → lo < hi → 0 < RoughRegime.Upper.intervalRho lo hi)
    :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z (incrementEntryPolynomial r lo hi T y m i)‖ ≤
      incrementComplexEnvelope r lo hi (intervalRho lo hi / η) L T y := by
  have hρ := h_RoughRegime_Upper_intervalRho_pos lo hi hlo hlt
  have hη : 0 < η := hρ.trans hρη
  have hq : 0 < intervalRho lo hi / η := div_pos hρ hη
  have hq1 : intervalRho lo hi / η < 1 := (div_lt_one hη).mpr hρη
  have hδ : 0 ≤ (4 * perturbationConstant η)⁻¹ :=
    (inv_pos.mpr (mul_pos (by norm_num) (h_NearlyMinimax_perturbationConstant_pos η hη hη1))).le
  have hsmall : 4 * (4 * perturbationConstant η)⁻¹ * perturbationConstant η ≤ 1 := by
    have hK := ne_of_gt (h_NearlyMinimax_perturbationConstant_pos η hη hη1)
    field_simp
    norm_num
  have hdA := h_NearlyMinimax_coordinate_normalized_perturbation r lo hi η hη hη1 z z₀ hz
    (currentCoordinateCLM r) (le_add_of_nonneg_right (norm_nonneg _))
  have hdC := h_NearlyMinimax_coordinate_normalized_perturbation r lo hi η hη hη1 z z₀ hz
    (parentCoordinateCLM r) (le_add_of_nonneg_left (norm_nonneg _))
  have hK := h_NearlyMinimax_complex_kernel_entry_coefficient_bound lo hi hlo hlt
    (currentCoordinateCLM r z₀) (currentCoordinateCLM r z) hA hASpec η _ hη hη1 hδ hsmall hdA
  have hD := h_NearlyMinimax_complex_kernel_entry_coefficient_bound lo hi hlo hlt
    (parentCoordinateCLM r z₀) (parentCoordinateCLM r z) hC hCSpec η _ hη hη1 hδ hsmall hdC
  have hzR : ∀ j, ‖z j‖ ≤ L + 1 := by
    intro j
    apply (norm_le_pi_norm z j).trans
    calc
      ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + L := add_le_add (hz.le.trans (min_le_left _ _)) hz₀
      _ = _ := by ring
  have hI (j : Fin r) :
      ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j))‖ ≤
        inverseComplexEnvelope r lo hi (intervalRho lo hi / η) := by
    rw [MvPolynomial.eval₂_rename, h_NearlyMinimax_coordinate_parent_valuation,
      h_NearlyMinimax_parentInverseEntryPolynomial_eval_complex, norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left
      (h_NearlyMinimax_combined_truncation_uniform_bound _ _ _ 4 hq hq1 (by norm_num) hK hD i j m)
      (abs_nonneg _)).trans_eq (by simp [inverseComplexEnvelope, mul_assoc])
  simp only [incrementEntryPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul]
  calc
    _ ≤ ∑ j : Fin r, ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j)) *
        MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin r, inverseComplexEnvelope r lo hi (intervalRho lo hi / η) *
        polynomialCoordinateBound (numeratorPolynomial r T y j) (L + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (hI j)
        (h_NearlyMinimax_polynomial_complex_coordinate_bound _ z (L + 1) (by positivity) hzR)
        (norm_nonneg _) (h_NearlyMinimax_inverseComplexEnvelope_nonneg r lo hi _ hq.le)
    _ = _ := by rw [← Finset.mul_sum]; rfl
end UniformNeighborhood
section ActualDerivatives
end ActualDerivatives
end NearlyMinimax
