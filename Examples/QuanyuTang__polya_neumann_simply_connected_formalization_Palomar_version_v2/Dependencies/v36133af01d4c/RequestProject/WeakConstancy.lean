module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v36133af01d4c.RequestProject.Defs
/-!
# Functions with vanishing weak gradient are constant

On a domain (connected open set) `Ω ⊂ ℂ`, an `L²(Ω)` function whose weak gradient vanishes is
a.e. equal to a constant. This is the step of the Poincaré–Wirtinger inequality that identifies
the limit of a minimizing sequence.

The proof mollifies: for a smooth bump `ρ` of radius `ε`, the convolution `u ⋆ ρ` is smooth,
and its derivative at `x` is `-∫_Ω u ∂ψ` for the test function `ψ = ρ(x - ·)`, hence zero
whenever `B̄(x, ε) ⊆ Ω`. So `u ⋆ ρ` is constant on small balls, and by the Lebesgue
differentiation theorem `u ⋆ ρ_ε → u` a.e., so `u` is a.e. constant on small balls; a
connectedness argument concludes.
-/
@[expose] public section
open MeasureTheory Filter Topology Metric
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
