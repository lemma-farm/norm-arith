module
/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/SpinGlass/FinitePartition.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/
public import Mathlib
public import Examples.pmaronow__fluctuations_palomar.Dependencies.v1bf3dd9e1628.SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.LogDerivatives
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
section FinitePartition
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]
end FinitePartition
end SK.Analytic
end
end
end
end
end
end
end SKConstantsOAI
