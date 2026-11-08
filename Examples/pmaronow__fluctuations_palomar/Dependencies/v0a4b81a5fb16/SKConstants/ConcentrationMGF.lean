module
public import Mathlib
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic
public section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace SKConstants.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
structure LocalQuadraticMGF (X : Ω → ℝ) (μ : Measure Ω) (v radius : ℝ) : Prop where
  integrable_exp_mul : ∀ t : ℝ, |t| ≤ radius →
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, |t| ≤ radius → mgf X μ t ≤ Real.exp (v * t ^ 2)
end SKConstants.Concentration
