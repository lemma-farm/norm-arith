module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.ReconBasic
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.ArcLength
/-!
# The Cauchy–Pompeiu formula for Lipschitz functions

For a Lipschitz compactly supported `F : ℂ → ℂ` and every `w`,

  `∫_ℂ ∂̄F(z) / (z - w) dz = -π F(w)`  (`integral_dbar_div_sub`).

The proof is in polar coordinates around `w`: there
`r e^{-it} ∂̄F = (∂_r G + (i/r) ∂_t G)/2` for `G(r, t) = F(w + r e^{it})`; the radial term
integrates to `-F(w)` and the angular term to `0`. Rademacher's theorem and Fubini's theorem
make the computation valid for Lipschitz `F`.
-/
@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real
noncomputable section
namespace PolyaNeumann
end PolyaNeumann
