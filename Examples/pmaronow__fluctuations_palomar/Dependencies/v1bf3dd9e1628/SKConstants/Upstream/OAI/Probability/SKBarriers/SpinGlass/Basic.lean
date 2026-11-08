module
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/SpinGlass/Basic.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
public import Mathlib
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Model
@[expose] public section
namespace SKConstantsOAI
section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK
def flip {n : ℕ} (x : Config n) : Config n := fun i => !(x i)
instance disorderLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderLaw n) := by
  unfold disorderLaw
  infer_instance
end SK
end
end
end
end SKConstantsOAI
