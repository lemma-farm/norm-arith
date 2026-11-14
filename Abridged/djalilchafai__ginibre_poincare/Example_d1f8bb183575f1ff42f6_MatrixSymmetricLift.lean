module

public import Mathlib
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Set.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Tactic.Positivity
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.InnerProductSpace.Calculus

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Concrete.Configuration ====
public section
@[expose] public section
/-!
# Configuration space and particle permutations

The configuration space of `n` planar particles is `Fin n → ℂ`.  This file
defines particle relabelling, symmetric and alternating observables, and the
collision locus.  It contains no measure-theoretic or analytic input.
-/
namespace GinibrePoincare
/-- The configuration space of `n` labelled particles in the complex plane. -/
abbrev Configuration (n : ℕ) := Fin n → ℂ
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Concrete.GaussianProbability ====
public section
@[expose] public section
/-!
# The normalized complex Gaussian probability measure

For `n` particles, each real coordinate has variance `1 / (2n)`.  We first
use Mathlib's normalized real Gaussian probability measure, take two
independent copies to obtain one complex coordinate, and then take the finite
product over the particle labels.

This construction proves the probability normalization without evaluating a
multidimensional integral.  Identification with the explicit density
`(n / π)^n exp (-n |z|²)` is deliberately kept as a separate theorem target in
`MeasureModel.lean`.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
/-- Variance of each real coordinate of the complex Gaussian reference law. -/
def realCoordinateVariance (n : ℕ) : NNReal :=
  ((2 : NNReal) * (n : NNReal))⁻¹
/-- Centered real Gaussian probability measure with variance `1 / (2n)`. -/
def realCoordinateGaussianProbability (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.gaussianReal 0 (realCoordinateVariance n), by
    infer_instance⟩
/-- One complex Gaussian coordinate, assembled from two independent real
coordinates of variance `1 / (2n)`. -/
def complexCoordinateGaussianProbability (n : ℕ) : ProbabilityMeasure ℂ :=
  (ProbabilityMeasure.pi
      (fun _ : Fin 2 => realCoordinateGaussianProbability n)).map
    Complex.measurableEquivPi.symm
/-- Product complex Gaussian probability measure on `ℂⁿ`. -/
def complexGaussianProbability (n : ℕ) :
    ProbabilityMeasure (Configuration n) :=
  ProbabilityMeasure.pi
    (fun _ : Fin n => complexCoordinateGaussianProbability n)

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixOverlap ====
public section
@[expose] public section
/-! # Spectral-projector overlap algebra

The overlap convention is exactly `O j k = Tr (P k * (P j)ᴴ)`.
These results are unconditional finite-dimensional algebra; they do not assert
the Ginibre spectral pushforward or eigenvalue differentiability.
-/
open scoped BigOperators ComplexOrder
open Matrix
namespace GinibrePoincare
noncomputable section
variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- The overlap Gram matrix, in the paper's index convention. -/
def matrixOverlap (P : ι → Matrix n n ℂ) : Matrix ι ι ℂ :=
  fun j k => Matrix.trace (P k * (P j)ᴴ)

/-- The overlap-weighted energy. -/
def matrixOverlapEnergy (P : ι → Matrix n n ℂ) (a : ι → ℂ) : ℝ :=
  (star a ⬝ᵥ (matrixOverlap P *ᵥ a)).re

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixGaussianMeasure ====
public section
@[expose] public section
/-! # Concrete complex Ginibre matrix Gaussian law

Rows are independent product Gaussian vectors; hence all matrix entries are
independent complex Gaussians with real-coordinate variance `(2n)⁻¹`.
The density is identified explicitly with `exp (-n Tr(GG*))`.
-/
open MeasureTheory
open scoped BigOperators ENNReal
namespace GinibrePoincare
noncomputable section
@[reducible] instance ginibreMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℂ))

def matrixGaussianProbability (n : ℕ) : ProbabilityMeasure (Matrix (Fin n) (Fin n) ℂ) :=
  ProbabilityMeasure.pi (fun _ : Fin n => complexGaussianProbability n)
def matrixGaussianMeasure (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  matrixGaussianProbability n

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixLocalEigenvalue ====
public section
@[expose] public section
/-! # Smooth local eigenvalue branches at simple spectrum

The complex implicit-function theorem applies to the characteristic equation
because a separable characteristic polynomial has a nonzero derivative at
each root. Local eigenvalues are constructed, rather than assumed.
-/
open scoped Topology ContDiff
open Matrix Filter
namespace GinibrePoincare
noncomputable section
abbrev GinibreMatrixCoordinates (n : ℕ) := Fin n → Fin n → ℂ

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixEigenvalueProjector ====
public section
@[expose] public section
/-! # Canonical adjugate spectral projectors and the eigenvalue differential -/
open scoped BigOperators Topology ContDiff
open Matrix Filter
namespace GinibrePoincare
noncomputable section

/-- Canonical simple-root spectral projector, with no choice of eigenvectors. -/
def matrixEigenvalueProjector (n : ℕ) (G : GinibreMatrixCoordinates n) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((Matrix.charpoly (Matrix.of G)).derivative.eval z)⁻¹ •
    (Matrix.scalar (Fin n) z - Matrix.of G).adjugate

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixLocalSpectrum ====
public section
@[expose] public section
/-! # Actual smooth local labeling of the full simple spectrum -/
open scoped Topology ContDiff
open Matrix Filter
namespace GinibrePoincare
noncomputable section

set_option linter.unusedVariables false in
axiom _root_.GinibrePoincare.matrix_exists_measurable_simple_labeling : ∀ (n : ℕ),
  ∃ (labels : GinibrePoincare.GinibreMatrixCoordinates n → Fin n → ℂ),
    Measurable labels ∧
      ∀ (A : Fin n → Fin n → ℂ),
        ((Matrix.of : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ) A).charpoly.Separable →
          Function.Injective (labels A) ∧
            ∀ (i : Fin n),
              Polynomial.eval (labels A i)
                  ((Matrix.of : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ) A).charpoly =
                0
end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixSpectralLaw ====
public section
@[expose] public section
/-! # The actual Gaussian matrix spectral pushforward

This constructs the law from the matrix ensemble. Identifying its density with the
Vandermonde density is a separate change-of-variables theorem.
-/
open MeasureTheory Matrix
set_option backward.isDefEq.respectTransparency false
namespace GinibrePoincare
noncomputable section
def matrixMeasurableEigenvalues (n : ℕ) : GinibreMatrixCoordinates n → Fin n → ℂ :=
  (matrix_exists_measurable_simple_labeling n).choose

def matrixSpectralMeasure (n : ℕ) : Measure (Fin n → ℂ) :=
  (matrixGaussianMeasure n).map (matrixMeasurableEigenvalues n)

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.GinibreEntropy ====
public section
@[expose] public section
/-! # Actual square entropy for the radial log-Sobolev problem
These are entropy and integrability results, not a log-Sobolev inequality.
-/
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
/-- Square entropy with its actual integral definition. -/
def squareEntropy {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ)

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.CompactLipschitzLSIExtension ====
public section
@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology Convolution NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual coordinate energy associated to any finite family of directions. -/
def directionalEnergy {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] (d : ι → E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, (fderiv ℝ f x (d i)) ^ 2

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.GaussianCurryLaw ====
public section
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- Linear currying of a finite family of real coordinates. -/
def gaussianCurryEquiv (I : Type*) (J : I → Type*) [Fintype I] [∀ i, Fintype (J i)] :
    ((Sigma J) → ℝ) ≃L[ℝ] (∀ i, J i → ℝ) where
  __ := LinearEquiv.piCurry ℝ (fun _ _ => ℝ)
  continuous_toFun := by
    change Continuous (fun x : Sigma J → ℝ => fun i j => x ⟨i, j⟩)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_apply (⟨i, j⟩ : Sigma J)
  continuous_invFun := by
    change Continuous (fun x : ∀ i, J i → ℝ => fun p : Sigma J => x p.1 p.2)
    apply continuous_pi
    intro p
    exact (continuous_apply p.2).comp (continuous_apply p.1)

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixGaussianLSI ====
public section
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev MatrixRealIndex (n : ℕ) := Σ _ : Fin n, Σ _ : Fin n, Fin 2
def matrixRealCoordinates (n : ℕ) :
    (MatrixRealIndex n → ℝ) ≃L[ℝ] (Fin n → Fin n → ℂ) :=
  (gaussianCurryEquiv (Fin n) (fun _ => Σ _ : Fin n, Fin 2)).trans
    (ContinuousLinearEquiv.piCongrRight (fun _ : Fin n =>
      (gaussianCurryEquiv (Fin n) (fun _ => Fin 2)).trans
        (ContinuousLinearEquiv.piCongrRight (fun _ : Fin n =>
          Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm))))

def matrixRealGradientEnergy (n : ℕ) (F : (Fin n → Fin n → ℂ) → ℝ) :
    (Fin n → Fin n → ℂ) → ℝ :=
  directionalEnergy (fun i : MatrixRealIndex n => matrixRealCoordinates n (Pi.single i 1)) F

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.MatrixRealDifferential ====
public section
@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
def realDifferentialWirtinger {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℝ) (i : Fin n) : ℂ :=
  ((L (Pi.single i 1) : ℂ) - Complex.I * (L (Pi.single i Complex.I) : ℂ)) / 2

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Examples.Example_d1f8bb183575f1ff42f6_MatrixSymmetricLift ====
@[expose] public section
open Filter Matrix MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
def matrixSymmetricLift (n : ℕ) (F : (Fin n → ℂ) → ℝ) : GinibreMatrixCoordinates n → ℝ :=
  F ∘ matrixMeasurableEigenvalues n

def matrixSpectralOverlapEnergy (n : ℕ) (F : (Fin n → ℂ) → ℝ)
    (A : GinibreMatrixCoordinates n) : ℝ :=
  matrixOverlapEnergy
    (fun i => matrixEigenvalueProjector n A (matrixMeasurableEigenvalues n A i))
    (realDifferentialWirtinger (fderiv ℝ F (matrixMeasurableEigenvalues n A)))
set_option linter.unusedVariables false in
/-- The actual overlap LSI under the Gaussian matrix spectral pushforward. The matrix
lift has the ordinary regularity needed by the sharp Gaussian LSI. -/
theorem matrixSpectral_overlap_lsi_compactLipschitz (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    {K : ℝ≥0} (hLip : LipschitzWith K (matrixSymmetricLift n F))
    (hc : HasCompactSupport (matrixSymmetricLift n F)) 
    (h_GinibrePoincare_squareEntropy_map : ∀ {α β : Type} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] (μ : MeasureTheory.Measure α)
      (T : α → β),
      AEMeasurable T μ →
        ∀ (f : β → ℝ),
          MeasureTheory.AEStronglyMeasurable (fun (y : β) ↦ f y ^ 2) (MeasureTheory.Measure.map T μ) →
            MeasureTheory.AEStronglyMeasurable (fun (y : β) ↦ f y ^ 2 * Real.log (f y ^ 2))
                (MeasureTheory.Measure.map T μ) →
              GinibrePoincare.squareEntropy (MeasureTheory.Measure.map T μ) f =
                GinibrePoincare.squareEntropy μ fun (x : α) ↦ f (T x))
    (h_GinibrePoincare_matrixGaussian_lsi_compactLipschitz : ∀ (n : ℕ),
      0 < n →
        ∀ (F : (Fin n → Fin n → ℂ) → ℝ) {K : NNReal},
          LipschitzWith K F →
            HasCompactSupport F →
              GinibrePoincare.squareEntropy (GinibrePoincare.matrixGaussianMeasure n) F ≤
                1 / (↑n : ℝ) *
                  ∫ (A : Matrix (Fin n) (Fin n) ℂ),
                    GinibrePoincare.matrixRealGradientEnergy n F
                      A ∂GinibrePoincare.matrixGaussianMeasure n)
    (h_GinibrePoincare_matrixSymmetricLift_energy : ∀ (n : ℕ) (A : GinibrePoincare.GinibreMatrixCoordinates n),
      ((Matrix.of : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ) A).charpoly.Separable →
        ∀ (F : (Fin n → ℂ) → ℝ),
          Differentiable ℝ F →
            (∀ (e : Fin n ≃ Fin n) (z : Fin n → ℂ), F (z ∘ (⇑e : Fin n → Fin n)) = F z) →
              GinibrePoincare.matrixRealGradientEnergy n (GinibrePoincare.matrixSymmetricLift n F) A =
                4 *
                  GinibrePoincare.matrixOverlapEnergy
                    (fun (i : Fin n) ↦
                      GinibrePoincare.matrixEigenvalueProjector n A
                        (GinibrePoincare.matrixMeasurableEigenvalues n A i))
                    (GinibrePoincare.realDifferentialWirtinger
                      (fderiv ℝ F (GinibrePoincare.matrixMeasurableEigenvalues n A))))
    (h_GinibrePoincare_matrixMeasurableEigenvalues_measurable : ∀ (n : ℕ), Measurable (GinibrePoincare.matrixMeasurableEigenvalues n))
    (h_GinibrePoincare_matrixGaussian_charpoly_separable_ae : ∀ (n : ℕ),
      ∀ᵐ (G : Matrix (Fin n) (Fin n) ℂ) ∂GinibrePoincare.matrixGaussianMeasure n, G.charpoly.Separable)
    (h_GinibrePoincare_continuous_square_mul_log : ∀ {α : Type} [inst : TopologicalSpace α] {f : α → ℝ},
      Continuous f → Continuous fun (x : α) ↦ f x ^ 2 * Real.log (f x ^ 2))
    :
    squareEntropy (matrixSpectralMeasure n) F ≤
      (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have hg := h_GinibrePoincare_matrixGaussian_lsi_compactLipschitz n hn (matrixSymmetricLift n F) hLip hc
  have hent : squareEntropy (matrixSpectralMeasure n) F =
      squareEntropy (matrixGaussianMeasure n) (matrixSymmetricLift n F) := by
    unfold matrixSpectralMeasure matrixSymmetricLift
    exact h_GinibrePoincare_squareEntropy_map _ _ (h_GinibrePoincare_matrixMeasurableEigenvalues_measurable n).aemeasurable F
      (hF.continuous.pow 2).aestronglyMeasurable
      (h_GinibrePoincare_continuous_square_mul_log hF.continuous).aestronglyMeasurable
  have he : (∫ A, matrixRealGradientEnergy n (matrixSymmetricLift n F) A
      ∂matrixGaussianMeasure n) =
        4 * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [h_GinibrePoincare_matrixGaussian_charpoly_separable_ae n] with A hA
    exact h_GinibrePoincare_matrixSymmetricLift_energy n A hA F hF hsym
  rw [hent]
  rw [he] at hg
  convert hg using 1 <;> ring
end
end GinibrePoincare
