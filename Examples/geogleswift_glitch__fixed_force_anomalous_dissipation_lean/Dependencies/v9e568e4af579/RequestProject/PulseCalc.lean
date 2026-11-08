module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.DriftRegularity
/-!
# Calculus for rescaled eigenfields

Derivatives of fields of the form `x ↦ a • F(k x - z)`, used for the isolated pulses of
Lemma 5.2.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end AnomDiss
