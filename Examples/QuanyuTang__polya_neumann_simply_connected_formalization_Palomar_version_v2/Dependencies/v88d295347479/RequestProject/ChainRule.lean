module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.MollifierL2
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.BiLipschitz
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.WeakCompact
/-!
# The Sobolev chain rule for bi-Lipschitz maps

For a homeomorphism `f` of the plane which is `K`-Lipschitz on an open set `Ω` with inverse
`K`-Lipschitz on `f(Ω)`, and `v ∈ H¹(f(Ω))` with weak gradient `G`, the function `u = v ∘ f` lies in
`H¹(Ω)` with weak gradient `∂_i u = ∑_j (∂_i f)_j (G_j ∘ f)`, i.e. `∇u = (Df)ᵀ (∇v ∘ f)`
(`isWeakGradient_comp_bilip`).

The proof mollifies `v`: `ψ_k = ρ_k ⋆ v` is smooth with `∇ψ_k = ρ_k ⋆ G` near `f(supp θ)`, the
chain rule for `ψ_k ∘ f` holds by integration by parts for Lipschitz functions (Rademacher), and
`ψ_k → v`, `∇ψ_k → G` in `L²` (`tendsto_mollify_L2`).
-/
@[expose] public section
open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal
noncomputable section
namespace PolyaNeumann
/-! ### Derivatives of mollifications of `H¹` functions -/
section BiLip
variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : ℝ≥0}
end BiLip
/-! ### The chain rule -/
section ChainRule
variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : ℝ≥0}
end ChainRule
end PolyaNeumann
end
