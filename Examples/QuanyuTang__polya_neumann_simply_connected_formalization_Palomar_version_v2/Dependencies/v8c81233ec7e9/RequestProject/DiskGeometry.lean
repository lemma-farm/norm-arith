module
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.SmoothDomain
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.Transport
/-!
# The actual unit disk and its positively oriented boundary

The disk is a smooth domain in the project's graph-chart definition. Its
local graph is constructed from `2y - y² - x² = 0`, and then extended by the
already proved smooth cutoff extension. The standard circle map has all
the fields of `IsBoundaryParam`, including the positive signed-area identity.
-/
@[expose] public section
noncomputable section
namespace PolyaNeumann
open MeasureTheory Set Metric
open scoped Real ContDiff ComplexConjugate
end PolyaNeumann
end
