module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.ArcLength
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.CurveContinuity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
/-!
# Lipschitz maps of the plane and of closed curves (tools for Section 10)

* `volume_image_eq_zero_of_lipschitzOnWith`: a Lipschitz map of the plane sends null sets to null
  sets;
* `abs_det_le_sq_norm`, `abs_det_fderiv_le`: `|det Df| ≤ ‖Df‖² ≤ K²` for a map that is
  `K`-Lipschitz on an open set;
* `volume_image_eq_lintegral`: change of variables `|f(Ω)| = ∫_Ω |det Df|` for maps that are
  Lipschitz and injective on an open set `Ω` (via Rademacher's theorem);
* `tendsto_integral_signedAreaDensity`: the signed-area integral `∫₀^{2π} Im(conj γ · γ')` is
  continuous under uniform convergence of uniformly Lipschitz `2π`-periodic curves.
-/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real Interval
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
end
