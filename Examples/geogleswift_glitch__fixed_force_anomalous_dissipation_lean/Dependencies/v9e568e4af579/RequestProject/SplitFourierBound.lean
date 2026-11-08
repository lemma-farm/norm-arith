module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitNegMoment
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitMeasurable
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitClose
/-!
# The weighted Fourier bound for the split maps

The per-`n` estimate in the proof of Proposition 3.11: Lemma 3.5 applied to the random maps
`Ψ_n` (canonical Lie splitting of `B_{μ,ω}` with Gaussian increments), with the negative moment
hypothesis inherited from Lemma 2.7 through Lemma 3.9.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal Matrix
noncomputable section
namespace AnomDiss
section SplitDefs
variable {L M : ℕ} {S : ℕ → ℝ}
end SplitDefs
end AnomDiss
