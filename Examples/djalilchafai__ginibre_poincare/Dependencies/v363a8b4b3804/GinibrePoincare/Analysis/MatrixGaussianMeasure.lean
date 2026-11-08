module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v363a8b4b3804.GinibrePoincare.Analysis.ComplexGaussianDensity
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
@[reducible] instance ginibreMatrixMeasureSpace (n : ℕ) :
    MeasureSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (MeasureSpace (Fin n → Fin n → ℂ))
def matrixGaussianProbability (n : ℕ) : ProbabilityMeasure (Matrix (Fin n) (Fin n) ℂ) :=
  ProbabilityMeasure.pi (fun _ : Fin n => complexGaussianProbability n)
def matrixGaussianMeasure (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  matrixGaussianProbability n
instance matrixGaussianMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (matrixGaussianMeasure n) := by
  unfold matrixGaussianMeasure
  infer_instance
end
end GinibrePoincare
