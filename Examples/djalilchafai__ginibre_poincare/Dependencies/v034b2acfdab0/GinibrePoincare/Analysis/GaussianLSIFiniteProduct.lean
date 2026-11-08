module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v034b2acfdab0.GinibrePoincare.Analysis.GaussianLSIProduct
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v034b2acfdab0.GinibrePoincare.Analysis.CompactLipschitzLSIExtension
@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- Recursive real coordinate space of dimension `n + 1`. -/
abbrev GaussianProductSpace : ℕ → Type
  | 0 => ℝ
  | n + 1 => GaussianProductSpace n × ℝ
instance (n : ℕ) : NormedAddCommGroup (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (NormedAddCommGroup ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (NormedAddCommGroup (GaussianProductSpace n × ℝ))
instance (n : ℕ) : NormedSpace ℝ (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (NormedSpace ℝ ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (NormedSpace ℝ (GaussianProductSpace n × ℝ))
instance (n : ℕ) : MeasurableSpace (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (MeasurableSpace (GaussianProductSpace n × ℝ))
instance (n : ℕ) : BorelSpace (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (BorelSpace ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (BorelSpace (GaussianProductSpace n × ℝ))
instance (n : ℕ) : SecondCountableTopology (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (SecondCountableTopology ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs (SecondCountableTopology (GaussianProductSpace n × ℝ))
/-- The actual product of `n + 1` centered Gaussians with variance `v`. -/
def gaussianProductLaw (v : ℝ≥0) : (n : ℕ) → Measure (GaussianProductSpace n)
  | 0 => gaussianReal 0 v
  | n + 1 => (gaussianProductLaw v n).prod (gaussianReal 0 v)
instance (v : ℝ≥0) (n : ℕ) : IsProbabilityMeasure (gaussianProductLaw v n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 v))
  | succ n ih => letI := ih; exact inferInstanceAs
      (IsProbabilityMeasure ((gaussianProductLaw v n).prod (gaussianReal 0 v)))
instance (n : ℕ) : FiniteDimensional ℝ (GaussianProductSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (FiniteDimensional ℝ ℝ)
  | succ n ih => letI := ih; exact inferInstanceAs
      (FiniteDimensional ℝ (GaussianProductSpace n × ℝ))
/-- Product Lebesgue (Haar) measure in the same recursive coordinate space. -/
def gaussianProductHaar : (n : ℕ) → Measure (GaussianProductSpace n)
  | 0 => volume
  | n + 1 => (gaussianProductHaar n).prod volume
instance (n : ℕ) : (gaussianProductHaar n).IsAddHaarMeasure := by
  induction n with
  | zero => exact inferInstanceAs (volume : Measure ℝ).IsAddHaarMeasure
  | succ n ih => letI := ih; exact inferInstanceAs
      (((gaussianProductHaar n).prod (volume : Measure ℝ)).IsAddHaarMeasure)
end
end GinibrePoincare
