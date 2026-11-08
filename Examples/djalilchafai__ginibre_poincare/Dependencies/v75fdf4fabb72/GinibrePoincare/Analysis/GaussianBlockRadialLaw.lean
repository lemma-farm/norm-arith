module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v75fdf4fabb72.GinibrePoincare.Analysis.RadialGradientTransfer
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v75fdf4fabb72.GinibrePoincare.Analysis.GinibreRadialGamma
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Pointwise
namespace GinibrePoincare
noncomputable section
/-- A `k`-dimensional complex Gaussian block with real variance `1/(2n)`. -/
def gaussianBlockMeasure (n k : ℕ) : Measure (Configuration k) :=
  Measure.pi (fun _ : Fin k => (complexCoordinateGaussianProbability n : Measure ℂ))
instance (n k : ℕ) : IsProbabilityMeasure (gaussianBlockMeasure n k) := by
  unfold gaussianBlockMeasure
  infer_instance
abbrev GaussianRadialBlocks (n : ℕ) := (i : Fin n) → Configuration (i.val + 1)
def gaussianRadialBlockMeasure (n : ℕ) : Measure (GaussianRadialBlocks n) :=
  Measure.pi (fun i : Fin n => gaussianBlockMeasure n (i.val + 1))
instance (n : ℕ) : IsProbabilityMeasure (gaussianRadialBlockMeasure n) := by
  unfold gaussianRadialBlockMeasure
  infer_instance
end
end GinibrePoincare
