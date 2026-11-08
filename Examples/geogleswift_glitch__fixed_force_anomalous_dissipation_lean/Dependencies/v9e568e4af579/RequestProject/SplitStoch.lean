module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitRep
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitRegular
/-!
# Gaussian moment estimates for the split maps

Second-moment computations for the Gaussian increments, used to compare the random split maps
`Ψ_n` with their deterministic counterpart (all increments set to zero).
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
section Tail
end Tail
section Stoch
variable {ψ : ℕ → Pt 2 → Pt 2} {ρ p β : ℝ} (n : ℕ) (v : ℝ≥0)
end Stoch
end AnomDiss
