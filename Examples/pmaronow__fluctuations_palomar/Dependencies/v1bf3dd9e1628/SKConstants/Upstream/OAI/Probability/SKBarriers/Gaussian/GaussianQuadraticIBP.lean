module
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/GaussianQuadraticIBP.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
public import Mathlib
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.SmoothObservables
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
theorem coordinateLinear_coordinateVector (n : ℕ) (a : Fin n → ℝ) :
    coordinateLinear n a (coordinateVector n a) = ∑ i, (a i)^2 := by
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    coordinateProjection_coordinateAxis,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,pow_two]
end SK.Analytic
end
end
end
end SKConstantsOAI
