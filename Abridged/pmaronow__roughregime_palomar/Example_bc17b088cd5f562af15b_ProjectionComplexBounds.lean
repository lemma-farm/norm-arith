module

public import Mathlib

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.Upper ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.MatrixUpper ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.MatrixDeterminant ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ComplexKernel ====
public section
@[expose] public section
/-! The actual reciprocal-kernel generating identity for arbitrary complex matrices. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial
namespace RoughRegime.ComplexKernel
open RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant RoughRegime.Upper

/-- The complex matrix kernel uses the same actual real coefficient polynomials. -/
def kernelCoefficient {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) (k : ℕ) : Matrix n n ℂ :=
  Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)

end RoughRegime.ComplexKernel

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.KernelExpressions ====
public section
@[expose] public section
/-! Uniform combined-index truncation bounds for actual finite kernel expressions. -/
noncomputable section
set_option maxHeartbeats 600000
universe u
open scoped BigOperators Matrix.Norms.L2Operator
open Set Metric
namespace RoughRegime.KernelExpressions
open RoughRegime.ComplexKernel
/-- All fixed finite sums and products of kernel entries and parameter polynomials. -/
inductive Expression (p : ℕ) {I : Type u} (dims : I → ℕ) : Type u
  | polynomial : MvPolynomial (Fin p) ℂ → Expression p dims
  | kernelEntry : (i : I) → Fin (dims i) → Fin (dims i) → Expression p dims
  | add : Expression p dims → Expression p dims → Expression p dims
  | mul : Expression p dims → Expression p dims → Expression p dims
/-- Actual common-index power series, retaining the entry polynomials proved earlier. -/
def Expression.series {p : ℕ} {I : Type*} {dims : I → ℕ}
    (lo hi : ℝ) (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (t : Fin p → ℂ) : Expression p dims → PowerSeries ℂ
  | .polynomial P => PowerSeries.C (MvPolynomial.eval t P)
  | .kernelEntry i a b => PowerSeries.mk (fun k => kernelCoefficient lo hi (M i t) k a b)
  | .add f g => f.series lo hi M t + g.series lo hi M t
  | .mul f g => f.series lo hi M t * g.series lo hi M t

end RoughRegime.KernelExpressions

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.KernelExpressionFinite ====
public section
@[expose] public section
/-! Actual finite sums, products and determinants as kernel expressions. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.KernelExpressions
variable {p : ℕ} {I : Type*} {dims : I → ℕ}
def finiteSum : {n : ℕ} → (Fin n → Expression p dims) → Expression p dims
  | 0, _ => .polynomial 0
  | n + 1, f => .add (f 0) (finiteSum (fun i => f i.succ))
def finiteProd : {n : ℕ} → (Fin n → Expression p dims) → Expression p dims
  | 0, _ => .polynomial 1
  | n + 1, f => .mul (f 0) (finiteProd (fun i => f i.succ))

def indexedSum {J : Type*} [Fintype J] (f : J → Expression p dims) : Expression p dims :=
  finiteSum (fun i : Fin (Fintype.card J) => f ((Fintype.equivFin J).symm i))
def indexedProd {J : Type*} [Fintype J] (f : J → Expression p dims) : Expression p dims :=
  finiteProd (fun i : Fin (Fintype.card J) => f ((Fintype.equivFin J).symm i))

def determinantExpression (i : I) : Expression p dims :=
  indexedSum (fun σ : Equiv.Perm (Fin (dims i)) =>
    .mul (.polynomial (MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ)))
      (indexedProd (fun j : Fin (dims i) => .kernelEntry i (σ j) j)))

end RoughRegime.KernelExpressions

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.CombinedPolynomial ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ProjectionApproximation ====
public section
@[expose] public section
/-! Concrete source Gram-residual polynomial approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial RealInnerProductSpace
namespace RoughRegime.ProjectionApproximation
open  RoughRegime.CombinedPolynomial


def polynomialEntryValuation {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ)) :
    Variables n dims → MvPolynomial σ ℝ
  | Sum.inl ab => Ω ab.1 ab.2
  | Sum.inr ⟨i, ab⟩ => M i ab.1 ab.2
def truncationPolynomialMatrix {σ : Type*} {N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial σ ℝ)) (m : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ) := fun a b =>
  MvPolynomial.eval₂Hom MvPolynomial.C (polynomialEntryValuation Ω M)
    (truncationEntryPolynomial n dims lo hi a b m)
def bilinearPolynomial {σ : Type*} {n : ℕ}
    (u : Fin n → MvPolynomial σ ℝ)
    (S : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (v : Fin n → MvPolynomial σ ℝ) : MvPolynomial σ ℝ := u ⬝ᵥ S.mulVec v
end RoughRegime.ProjectionApproximation

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ComplexDerivativeBridge ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v1df56198e41c.RoughRegime.ProjectionComplex ====
public section
@[expose] public section
/-! Uniform complex bounds for the actual substituted projection polynomials. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionComplex
open RoughRegime.KernelExpressions 
open RoughRegime.CombinedPolynomial RoughRegime.ProjectionApproximation
open RoughRegime.Upper RoughRegime.ComplexDerivativeBridge
 def complexEvaluation {σ : Type*} (t : σ → ℂ) : MvPolynomial σ ℝ →+* ℂ :=
  MvPolynomial.eval₂Hom Complex.ofRealHom t

def kernelFamilyDims {N : ℕ} (n : ℕ) (dims : Fin N → ℕ) : Option (Fin N) → ℕ
  | none => n
  | some i => dims i
def kernelFamily {p N n : ℕ} {dims : Fin N → ℕ}
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ)) :
    (i : Option (Fin N)) → (Fin p → ℂ) →
      Matrix (Fin (kernelFamilyDims n dims i)) (Fin (kernelFamilyDims n dims i)) ℂ
  | none, t => Ω.map (complexEvaluation t)
  | some i, t => (M i).map (complexEvaluation t)
def entryExpression {p N n : ℕ} (dims : Fin N → ℕ) (lo hi : ℝ) (a b : Fin n) :
    Expression p (kernelFamilyDims n dims) :=
  .mul (.polynomial (C ((intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ : ℝ)))
    (.mul (.kernelEntry none a b)
      (indexedProd (fun i : Fin N => determinantExpression (some i))))

end RoughRegime.ProjectionComplex

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_bc17b088cd5f562af15b_ProjectionComplexBounds ====
@[expose] public section
/-! Degree-independent complex bounds for the concrete bilinear approximants. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MvPolynomial
namespace RoughRegime.ProjectionComplex
open RoughRegime.KernelExpressions RoughRegime.ProjectionApproximation
open RoughRegime.ComplexDerivativeBridge


set_option linter.unusedVariables false in
/-- The fixed residual polynomials and every actual combined-index matrix
truncation have one common complex neighborhood and bound. Consequently the
actual scalar bilinear polynomial is uniformly bounded independently of `m`. -/
theorem uniform_bilinear_truncations {p N n : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (V : Set (Fin p → ℂ)) (hV : Bornology.IsBounded V)
    (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ))
    (hHerm : ∀ i t, t ∈ V → (kernelFamily Ω M i t).IsHermitian)
    (hSpec : ∀ i t, t ∈ V → spectrum ℝ (kernelFamily Ω M i t) ⊆ Set.Icc lo hi)
    (u v : Fin n → MvPolynomial (Fin p) ℝ) 
    (h_RoughRegime_ProjectionComplex_bilinearPolynomial_complex_bound : ∀ {p n : ℕ} (t : Fin p → ℂ) (u v : Fin n → MvPolynomial (Fin p) ℝ)
      (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ)) (A : ℝ),
      0 ≤ A →
        (∀ (i : Fin n),
            ‖(MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
                  (RoughRegime.ComplexDerivativeBridge.complexify (u i))‖ ≤
              A) →
          (∀ (i : Fin n),
              ‖(MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
                    (RoughRegime.ComplexDerivativeBridge.complexify (v i))‖ ≤
                A) →
            (∀ (i j : Fin n),
                ‖(MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
                      (RoughRegime.ComplexDerivativeBridge.complexify (S i j))‖ ≤
                  A) →
              ‖(MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
                    (RoughRegime.ComplexDerivativeBridge.complexify
                      (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v))‖ ≤
                (↑n : ℝ) ^ 2 * A ^ 3)
    (h_RoughRegime_ProjectionComplex_truncationPolynomialMatrix_complex_eval : ∀ {p N n : ℕ} {dims : Fin N → ℕ} (lo hi : ℝ) (Ω : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
      (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) (MvPolynomial (Fin p) ℝ)) (t : Fin p → ℂ)
      (m : ℕ) (a b : Fin n),
      (RoughRegime.ProjectionComplex.complexEvaluation t : MvPolynomial (Fin p) ℝ → ℂ)
          (RoughRegime.ProjectionApproximation.truncationPolynomialMatrix lo hi Ω M m a b) =
        ∑ k ∈ Finset.range (m + 1),
          (PowerSeries.coeff k : PowerSeries ℂ → ℂ)
            (RoughRegime.KernelExpressions.Expression.series lo hi
              (RoughRegime.ProjectionComplex.kernelFamily Ω M) t
              (RoughRegime.ProjectionComplex.entryExpression dims lo hi a b)))
    (h_RoughRegime_ProjectionComplex_complexEvaluation_continuous : ∀ {p : ℕ} (P : MvPolynomial (Fin p) ℝ),
      Continuous fun (t : Fin p → ℂ) ↦
        (RoughRegime.ProjectionComplex.complexEvaluation t : MvPolynomial (Fin p) ℝ → ℂ) P)
    (h_RoughRegime_ProjectionComplex_complexEvaluation_eq : ∀ {p : ℕ} (t : Fin p → ℂ) (P : MvPolynomial (Fin p) ℝ),
      (RoughRegime.ProjectionComplex.complexEvaluation t : MvPolynomial (Fin p) ℝ → ℂ) P =
        (MvPolynomial.eval t : MvPolynomial (Fin p) ℂ → ℂ)
          (RoughRegime.ComplexDerivativeBridge.complexify P))
    (h_RoughRegime_KernelExpressions_uniform_finite_expression_truncations : ∀ {p : ℕ} {I J : Type} {dims : I → ℕ} [Fintype J] (lo hi : ℝ),
      0 < lo →
        lo < hi →
          ∀ (V : Set (Fin p → ℂ)),
            Bornology.IsBounded V →
              ∀ (M : (i : I) → (Fin p → ℂ) → Matrix (Fin (dims i)) (Fin (dims i)) ℂ),
                (∀ (i : I), Continuous (M i)) →
                  (∀ (i : I), ∀ t ∈ V, (M i t).IsHermitian) →
                    (∀ (i : I), ∀ t ∈ V, spectrum ℝ (M i t) ⊆ Set.Icc lo hi) →
                      ∀ (f : J → RoughRegime.KernelExpressions.Expression p dims),
                        ∃ (ε : ℝ) (C : ℝ),
                          0 < ε ∧
                            ε ≤ 1 ∧
                              0 ≤ C ∧
                                ∀ (t : Fin p → ℂ),
                                  (∃ t0 ∈ V, ‖t - t0‖ < ε) →
                                    ∀ (j : J) (m : ℕ),
                                      ‖∑ k ∈ Finset.range (m + 1),
                                            (PowerSeries.coeff k : PowerSeries ℂ → ℂ)
                                              (RoughRegime.KernelExpressions.Expression.series lo hi M t
                                                (f j))‖ ≤
                                        C)
    :
    ∃ ε A : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ A ∧
      ∀ t, (∃ t0 ∈ V, ‖t - t0‖ < ε) →
        (∀ i, ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A) ∧
        (∀ i, ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A) ∧
        (∀ m i j, ‖MvPolynomial.eval t
          (complexify (truncationPolynomialMatrix lo hi Ω M m i j))‖ ≤ A) ∧
        (∀ m, ‖MvPolynomial.eval t (complexify
          (bilinearPolynomial u (truncationPolynomialMatrix lo hi Ω M m) v))‖ ≤
            (n : ℝ) ^ 2 * A ^ 3) := by
  let f : ((Fin n ⊕ Fin n) ⊕ (Fin n × Fin n)) → Expression p (kernelFamilyDims n dims)
    | Sum.inl (Sum.inl i) => .polynomial (complexify (u i))
    | Sum.inl (Sum.inr i) => .polynomial (complexify (v i))
    | Sum.inr ij => entryExpression dims lo hi ij.1 ij.2
  have hM : ∀ i, Continuous (kernelFamily Ω M i) := by
    intro i
    cases i <;> exact continuous_pi (fun a => continuous_pi (fun b => h_RoughRegime_ProjectionComplex_complexEvaluation_continuous _))
  obtain ⟨ε, A, hε, hε1, hA, hb⟩ := h_RoughRegime_KernelExpressions_uniform_finite_expression_truncations
    lo hi hlo hlt V hV (kernelFamily Ω M) hM hHerm hSpec f
  refine ⟨ε, A, hε, hε1, hA, ?_⟩
  intro t ht
  have hu (i : Fin n) : ‖MvPolynomial.eval t (complexify (u i))‖ ≤ A := by
    simpa [f, Expression.series] using hb t ht (Sum.inl (Sum.inl i)) 0
  have hv (i : Fin n) : ‖MvPolynomial.eval t (complexify (v i))‖ ≤ A := by
    simpa [f, Expression.series] using hb t ht (Sum.inl (Sum.inr i)) 0
  have hS (m : ℕ) (i j : Fin n) :
      ‖MvPolynomial.eval t (complexify (truncationPolynomialMatrix lo hi Ω M m i j))‖ ≤ A := by
    rw [← h_RoughRegime_ProjectionComplex_complexEvaluation_eq, h_RoughRegime_ProjectionComplex_truncationPolynomialMatrix_complex_eval]
    exact hb t ht (Sum.inr (i, j)) m
  exact ⟨hu, hv, hS, fun m => h_RoughRegime_ProjectionComplex_bilinearPolynomial_complex_bound t u v _ A hA hu hv (hS m)⟩
end RoughRegime.ProjectionComplex
