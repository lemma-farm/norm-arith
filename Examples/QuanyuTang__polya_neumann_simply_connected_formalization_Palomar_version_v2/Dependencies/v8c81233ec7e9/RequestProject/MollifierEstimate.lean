module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.WeakConstancy
/-!
# Mollifier estimates for `H¹` functions

For `u ∈ L²(Ω)` with weak gradient `g`, extended by zero to `U : ℂ → ℂ`, and a probability
density `ρ` supported in `{‖z‖ ≤ R}`, the mollification `ρ ⋆ U` is close to `U` in `L²` on
every open set `W` from which all segments `t - s z` (`t ∈ W`, `z ∈ supp ρ`, `0 ≤ s ≤ 1`)
stay inside `Ω`:
`‖1_W (U - ρ ⋆ U)‖_{L²} ≤ R (‖g₀‖ + ‖g₁‖)`.

The proof is by duality: the pairing of `U - ρ ⋆ U` with a test function is computed with the
fundamental theorem of calculus along segments and the definition of the weak gradient, and an
`L²` function whose pairings with test functions supported in `W` are bounded by `C ‖φ‖` has
norm at most `C`.
-/
@[expose] public section
open MeasureTheory Filter Topology Metric Set
open scoped Manifold
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
