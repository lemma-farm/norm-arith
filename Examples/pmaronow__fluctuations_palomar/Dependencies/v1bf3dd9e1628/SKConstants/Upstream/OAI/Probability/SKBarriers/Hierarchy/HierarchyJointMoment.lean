module
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Hierarchy/HierarchyJointMoment.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
public import Mathlib
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.CoordinateSigns
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
def coordinateProjection : (n : ℕ) → Fin n → ParameterSpace n →L[ℝ] ℝ
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (ContinuousLinearMap.snd ℝ (ParameterSpace n) ℝ)
      (fun j => (coordinateProjection n j).comp (ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ)) i
def coordinateLinear (n : ℕ) (a : Fin n → ℝ) : ParameterSpace n →L[ℝ] ℝ :=
  ∑ i, a i • coordinateProjection n i
theorem coordinateLinear_apply (n : ℕ) (a : Fin n → ℝ) (z : ParameterSpace n) :
    coordinateLinear n a z = ∑ i, a i*coordinateProjection n i z := by
  simp [coordinateLinear]
end SK.Analytic
end
end
end
end
end
end
end SKConstantsOAI
