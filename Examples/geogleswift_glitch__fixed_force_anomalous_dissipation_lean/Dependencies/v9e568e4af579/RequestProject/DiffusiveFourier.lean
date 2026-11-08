module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitFourierBound
/-!
# Proposition 3.11: the diffusive Fourier drift estimate

The time-one Fourier coefficients of a cell solution are limits of the averaged coefficients
`𝔼_ζ c_m^{Ψ_n}(ξ)` of the split maps; Jensen's inequality and Fatou's lemma then transfer the
per-`n` weighted Fourier bound for the split maps to the cell solution.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
section SplitHelpers
variable {L M : ℕ} {S : ℕ → ℝ}
end SplitHelpers
end AnomDiss
