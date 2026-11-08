module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.LipschitzChange
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v8c81233ec7e9.RequestProject.Defs
/-!
# Bi-Lipschitz changes of variables and the `L²` pullback

For a homeomorphism `f` of the plane which is `K`-Lipschitz on an open set `Ω` and whose inverse
is `K`-Lipschitz on `f(Ω)`:

* `ae_inv_sq_le_abs_det`: `|det Df| ≥ K⁻²` almost everywhere on `Ω`;
* `quasiMeasurePreserving_restrict`, `quasiMeasurePreserving_symm_restrict`: `f` and `f⁻¹` are
  quasi-measure-preserving between `Ω` and `f(Ω)`;
* `lintegral_image_bilip`, `integral_image_bilip`: the change of variables formulas
  `∫_{f(Ω)} g = ∫_Ω |det Df| g ∘ f`;
* `bilipPull`: the pullback `L²(f(Ω)) ≃ L²(Ω)`, `v ↦ v ∘ f`, with
  `⟨v, w⟩_{L²(f(Ω))} = ∫_Ω |det Df| ⟨v ∘ f, w ∘ f⟩` (`inner_eq_integral_bilipPull`).
-/
@[expose] public section
open MeasureTheory Filter Topology Set
noncomputable section
namespace PolyaNeumann
variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : NNReal}
end PolyaNeumann
end
