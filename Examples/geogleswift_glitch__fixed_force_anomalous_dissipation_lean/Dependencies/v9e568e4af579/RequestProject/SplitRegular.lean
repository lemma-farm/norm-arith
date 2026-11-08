module
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitSmooth
public import Examples.geogleswift_glitch__fixed_force_anomalous_dissipation_lean.Dependencies.v9e568e4af579.RequestProject.SplitConvergence
/-!
# Regularity of the canonical split maps

The `C²` bounds of Lemma 3.8 for the canonical splitting: each step is the flow of a smooth
field over a time `1/n`, hence `1/n`-close to the identity in `C²`, and the bounds survive the
`n`-fold composition.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal
noncomputable section
namespace AnomDiss
section Comp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
end Comp
section Iter
end Iter
section Lift
end Lift
section Canon
variable {L M : ℕ} {S : ℕ → ℝ}
end Canon
end AnomDiss
