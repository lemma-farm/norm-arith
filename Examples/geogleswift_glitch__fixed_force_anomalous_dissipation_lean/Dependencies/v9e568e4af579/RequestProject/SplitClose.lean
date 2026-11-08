module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitStoch
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.FlowStab
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitNegMoment
/-!
# Closeness of the split maps to the terminal flow map (derivative part of Lemma 3.9)

For every `x`, `𝔼_ζ ‖DΨ_n(x) - DΨ₀(x)‖ ≤ C √μ`, uniformly in `μ ∈ [0,1]`, `ω` and `n ≥ 1`.
The deviation splits into a stochastic part (the Gaussian increments, controlled in mean square)
and a deterministic part (the damping, controlled by `C¹` stability of flows).
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
variable {L M : ℕ} {S : ℕ → ℝ}
end AnomDiss
