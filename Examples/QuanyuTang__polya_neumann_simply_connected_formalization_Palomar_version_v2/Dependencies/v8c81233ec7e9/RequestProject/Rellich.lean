module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.RellichCompact
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.LipschitzCover
/-!
# Rellich compactness and closedness of the weak gradient

* `rellich_compact`: the Rellich–Kondrachov compactness theorem for bounded Lipschitz domains
  (part of External theorem E2 of the paper), stated for sequences: a sequence bounded in
  `H¹(Ω)` has an `L²(Ω)`-convergent subsequence. It is proved from the cover of `Ω` by
  shiftable pieces (`lipschitz_cover`) and the Kolmogorov–Riesz argument `rellich_of_cover`.
* `isWeakGradient_of_tendsto`: weak gradients are closed under `L²` limits.
* `isWeakGradient_smul`: weak gradients are compatible with scalar multiplication.
* `tendsto_integral_mul`: `u ↦ ∫_Ω u ψ` is continuous on `L²(Ω)` for `ψ ∈ L²(Ω)`.
-/
@[expose] public section
open MeasureTheory Filter Topology
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
