module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.BernoulliCubeLSI
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Bernoulli
@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section
/-- The fair law on the two signs. -/
def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1 / 2, by constructor <;> norm_num⟩
instance rademacherMeasure_probability : IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance
/-- Independent fair signs on the countable product probability space. -/
def rademacherProduct : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => rademacherMeasure)
instance rademacherProduct_probability : IsProbabilityMeasure rademacherProduct := by
  unfold rademacherProduct
  infer_instance
end
end GinibrePoincare
