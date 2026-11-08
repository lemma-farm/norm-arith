module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.JordanWinding
/-!
# Lipschitz charts of a planar boundary

Basic facts about the Lipschitz charts of a Lipschitz domain `Ω ⊂ ℂ`:

* graph points of a chart are boundary points (`chartPt_mem_frontier`), and boundary points in a
  chart box are graph points (`eq_chartPt_of_frontier`);
* recentering of a chart at a nearby boundary point (`isChartAt_recenter`) and uniform charts
  for bounded Lipschitz domains (`exists_uniform_charts`);
* a continuous function that is "strictly increasing from the left" at every point of an interval
  is strictly increasing (`strictMonoOn_of_local_left`);
* **consistency of orientation** (`chart_orient`): along the boundary, the abscissa of one chart
  is a strictly increasing function of the abscissa of any other chart (the domain lies on the
  left in both).
-/
@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
