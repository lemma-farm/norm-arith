module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.FlowDeriv
/-!
# `C²` regularity of flow maps

Assembly of the variational estimates: the flow maps of a `C2Field` are `C²`, with explicit
bounds on `DΦ - I` and `D²Φ` in terms of the elapsed time.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped NNReal
noncomputable section
namespace AnomDiss
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {V : ℝ → E → E} {M K : ℝ≥0} {K2 K3 : ℝ} {t₀ t₁ : ℝ}
end AnomDiss
