module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.BoundaryWalk
/-!
# The boundary walk closes up into a Lipschitz Jordan curve

For a bounded Lipschitz domain, the boundary walk (`walk`) eventually revisits a point
(`WalkData.exists_pair`, by compactness of `∂Ω`), hence returns to its starting point
(`WalkData.exists_return`, by backward uniqueness of the walk, which comes from consistency of
orientation). Stopping at the first return gives a closed Lipschitz curve, injective before the
return (`WalkData.exists_loop`), whose image is open and closed in `∂Ω`
(`WalkData.image_eq`). Hence, when `∂Ω` is connected, it is a single Lipschitz Jordan curve
(`exists_jordanParam_of_isPreconnected_frontier`).
-/
@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
section Loop
variable {Ω : Set ℂ} {ρ H : ℝ} {K : NNReal} {ch : ℂ → ℂ × (ℝ → ℝ)} {ℓ : ℝ} {p₀ : ℂ}
end Loop
end PolyaNeumann
