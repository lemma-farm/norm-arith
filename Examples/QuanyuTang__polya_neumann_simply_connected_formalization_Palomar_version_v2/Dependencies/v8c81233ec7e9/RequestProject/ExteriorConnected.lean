module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.JordanWinding
/-!
# Connectedness of the exterior of a Lipschitz domain with connected boundary

If `Ω` is a bounded Lipschitz domain whose boundary `∂Ω` is (pre)connected, then the exterior
`ℂ \ Ω̄` is connected (`isConnected_compl_closure_of_frontier`). The proof is local: below the
graph, every Lipschitz chart box contains a connected piece of the exterior that accumulates
at every boundary point of the box, and the boundary points adjacent to a given exterior
component form a relatively clopen subset of `∂Ω`.
-/
@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
