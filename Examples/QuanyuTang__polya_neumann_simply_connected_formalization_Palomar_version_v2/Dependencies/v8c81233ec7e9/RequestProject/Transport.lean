module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.Shift
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.Defs
/-!
# Boundary transport and its monodromy (Sections 4 and 10 of the paper)

For a closed Lipschitz boundary curve `γ : [0, L] → ∂Ω` (`L = 2π`) and an energy
`E = k² > 0`, the transport `W_E` solves
`W_E' = C_E W_E`, `W_E(0) = I`, with
`C_E(θ) = -(i k / 2) (γ'(θ) S_N^* + conj (γ'(θ)) S_N)`,
and the monodromy is `U_E = V_E^*`, `V_E = W_E(L)`.
We phrase the differential equation in its integral form, which is the meaning of the
almost-everywhere equation for absolutely continuous solutions.
-/
@[expose] public section
open scoped ComplexConjugate Real
open MeasureTheory
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
