module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.MollifierEstimate
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
/-!
# `L²` convergence of mollifications

For a normalized bump function `ρ = φ.normed volume` and `H ∈ L²(ℂ)`:

* `eLpNorm_mollify_le`: `‖ρ ⋆ H‖₂ ≤ ‖H‖₂` (Young's inequality for a probability kernel);
* `tendsto_mollify_L2`: `ρ_k ⋆ H → H` in `L²(ℂ)` when the radii of the bumps tend to `0`.
-/
@[expose] public section
open MeasureTheory Filter Topology Metric Set
open scoped ENNReal
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
