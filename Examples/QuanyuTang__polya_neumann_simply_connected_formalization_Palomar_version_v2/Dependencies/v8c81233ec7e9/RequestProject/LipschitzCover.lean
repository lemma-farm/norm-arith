module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.Defs
/-!
# A cover of a bounded Lipschitz domain by shiftable pieces

A bounded Lipschitz domain `Ω` is covered by finitely many open sets `W_j ⊆ Ω` such that, for
every `η > 0`, each `W_j` admits a closed ball `B̄(a_j, r_j)` with `‖a_j‖ + r_j ≤ η` of
admissible shifts: all segments `t - s z` (`t ∈ W_j`, `z ∈ B̄(a_j, r_j)`, `0 ≤ s ≤ 1`) stay in
`Ω`. Near the boundary the shifts point into the domain, inside a cone around the inward
direction of a Lipschitz chart; away from the boundary any small shift works.
-/
@[expose] public section
open Filter Topology Metric Set
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
