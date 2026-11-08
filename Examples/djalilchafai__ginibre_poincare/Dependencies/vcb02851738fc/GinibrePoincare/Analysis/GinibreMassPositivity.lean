module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vcb02851738fc.GinibrePoincare.Analysis.ComplexGaussianDensity
public import Mathlib.MeasureTheory.Measure.OpenPos
@[expose] public section
/-! # Strict positivity of the Ginibre normalizing mass -/
open MeasureTheory
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section
/-- The Vandermonde polynomial is continuous on configuration space. -/
theorem continuous_vandermonde {n : ℕ} :
    Continuous (vandermonde : Configuration n → ℂ) := by
  rw [show (vandermonde : Configuration n → ℂ) =
      fun z ↦ ∏ i : Fin n, ∏ j > i, (z j - z i) by
    funext z
    exact vandermonde_eq_product z]
  fun_prop
/-- The extended nonnegative Vandermonde density is measurable. -/
theorem measurable_vandermondeDensity {n : ℕ} :
    Measurable (vandermondeDensity : Configuration n → ℝ≥0∞) := by
  unfold vandermondeDensity vandermondeWeight
  exact ENNReal.measurable_ofReal.comp
    (Complex.continuous_normSq.comp continuous_vandermonde).measurable
end
end GinibrePoincare
