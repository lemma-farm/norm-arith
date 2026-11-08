module
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/SmoothObservables.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
public import Mathlib
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianResponse
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Calculus.CoordinateStein
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.HierarchyDensity
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
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SmoothObservables
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem HasExpGrowth.const (c : F) : HasExpGrowth (fun _ : E => c) :=
  HasExpGrowth.of_bounded (norm_nonneg c) (fun _ => le_rfl)
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem HasExpGrowth.fderiv_mul {f g : E → ℝ} (hc : Differentiable ℝ f) (hcg : Differentiable ℝ g)
    (hf : HasExpGrowth f) (hg : HasExpGrowth g) (hdf : HasExpGrowth (fderiv ℝ f))
    (hdg : HasExpGrowth (fderiv ℝ g)) : HasExpGrowth (fderiv ℝ (fun z => f z*g z)) := by
  have he : fderiv ℝ (fun z => f z*g z) = fun z => g z • fderiv ℝ f z+f z • fderiv ℝ g z := by
    funext z
    rw [fderiv_fun_mul (hc z) (hcg z)]
    exact add_comm _ _
  rw [he]
  exact (hg.smul hdf).add (hf.smul hdg)
end SmoothObservables
section SharedPrefix
variable {S : Type} [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
end SharedPrefix
end SK.Analytic
end
end
end
end
end
end
end
end SKConstantsOAI
