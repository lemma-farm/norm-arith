module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.WindingJump
/-!
# Orientation of a Lipschitz Jordan boundary

Let `Ω` be a bounded Lipschitz domain and `γ` a Lipschitz, `2π`-periodic parametrization of
`∂Ω`, injective on `[0, 2π)`, such that the exterior `ℂ \ Ω̄` is connected. Then the winding
number of `γ` is a constant `σ = ±1` on `Ω` and vanishes off `Ω̄`
(`windingNumber_pm_one_of_jordan`). The value `±1` comes from the jump of the winding number
across the boundary at a chart point (`windingNumber_jump`).
-/
@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
