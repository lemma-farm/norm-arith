module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.ScalarStages
/-!
# Parabolic Hölder regularity of smooth periodic drifts

A drift `V(t,x)` which is jointly `C²` and `ℤ²`-periodic in `x` belongs to `C^{β/2,1+β}` on
`[0,T] × 𝕋²` for every `0 < β < 1`.  This is applied to the isolated pulses of Section 5.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff
noncomputable section
namespace AnomDiss
section generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end generic
/-! ### Drifts built from the eigenfields -/
end AnomDiss
