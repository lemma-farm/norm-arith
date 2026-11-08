module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.ControlsAssembly
/-!
# Lemma 2.13: the terminal map and the control family

The controls of `ControlsAssembly` are the concatenation of `4L` shear pieces followed by four
zero-integral corrections; their flow is computed piece by piece.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
variable (L M : ℕ)
end AnomDiss
