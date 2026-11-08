module
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.ArcLength
/-!
# Green's formula through winding numbers

For a Lipschitz curve `γ : ℝ → ℂ` define the winding number
`wind(γ, z) = (2πi)⁻¹ ∫₀^{2π} γ'(θ) / (γ(θ) - z) dθ`.

* `PolyaNeumann.integral_ball_inv_sub`: the Cauchy transform of a disc,
  `∫_{|z| < R} (w - z)⁻¹ dz = π w̄` for `|w| < R`;
* `PolyaNeumann.integral_ball_windingNumber`: if `γ([0, 2π]) ⊂ {|z| < R}`, then
  `∫_{|z| < R} wind(γ, z) dz = (2i)⁻¹ ∫₀^{2π} conj(γ) γ'`;
* `PolyaNeumann.volume_image_Icc_eq_zero`: a Lipschitz curve has planar measure zero.

Together these give Green's formula `∫₀^{2π} Im(conj γ · γ') = ±2|Ω|` for a Jordan
parametrization of `∂Ω` whose winding number is `±1` on `Ω` and `0` off `Ω̄`.
-/
@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
