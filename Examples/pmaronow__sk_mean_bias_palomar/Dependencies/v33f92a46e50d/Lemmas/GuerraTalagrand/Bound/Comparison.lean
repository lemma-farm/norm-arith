module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import Examples.pmaronow__sk_mean_bias_palomar.Dependencies.v33f92a46e50d.Lemmas.GuerraTalagrand.Bound.FiniteState
public import Mathlib
set_option autoImplicit true
set_option linter.deprecated false
@[expose] public section
open MeasureTheory ProbabilityTheory Real BigOperators Filter Topology
open PhysLean.Probability.GaussianIBP
open scoped ContDiff ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace SpinGlass.AT
/-- The linear field whose value at state `ξ` is `⟪A ξ, z⟫`. -/
noncomputable def gtCoefficientCLM
    {S I : Type*} [Fintype S] [Fintype I]
    (A : S → EuclideanSpace ℝ I) :
    EuclideanSpace ℝ I →L[ℝ] GTStateSpace S :=
  ∑ ξ : S, (ContinuousLinearMap.innerSL ℝ (A ξ)).smulRight
    ((EuclideanSpace.basisFun S ℝ) ξ)
end SpinGlass.AT
