module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.FixedSpace
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.ChainRule
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.WeakCompact
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.GreenWinding
/-!
# Basic notions for the Cauchy reconstruction (Lemma 4.8)

* `lap φ` : the Laplacian `∂ₓ² φ + ∂ᵧ² φ` written with real Fréchet derivatives;
* `dbar F` : the Wirtinger derivative `∂̄F = (∂ₓF + i ∂ᵧF)/2`;
* `ePlane ξ` : the Fourier character `z ↦ e^{-2πi⟨z, ξ⟩}`;
* `doubleLayer γ h φ` : the double-layer pairing `∫₀^{2π} h(θ) Dφ(γ(θ))(-iγ'(θ)) dθ`;
* `IsWeakGradOn D w g` : `g` is a weak gradient of `w` on the open set `D`, tested against
  smooth compactly supported functions with support in `D` (integrals over `ℂ`).
-/
@[expose] public section
open MeasureTheory Set Filter
open scoped ComplexConjugate Real
noncomputable section
namespace PolyaNeumann
lemma TestFunction.const_mul {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) (c : ℂ) :
    TestFunction D (fun z => c * φ z) :=
  ⟨contDiff_const.mul hφ.1, hφ.2.1.mul_left, (tsupport_mul_subset_right).trans hφ.2.2⟩
end PolyaNeumann
