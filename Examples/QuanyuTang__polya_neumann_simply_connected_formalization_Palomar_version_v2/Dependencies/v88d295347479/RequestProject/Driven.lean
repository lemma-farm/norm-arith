module
public import Examples.QuanyuTang__polya_neumann_simply_connected_formalization_Palomar_version_v2.Dependencies.v88d295347479.RequestProject.CurveContinuity
/-!
# Driven transport equations and their endpoint identities (Lemma 4.10)

For a Lipschitz curve `γ`, an energy `E` and the transport `W = W_E`, consider an
`ℓ²(ℕ₀)`-valued solution `y` of the driven equation `y' = C_E y + f` (in integral form).
Variation of constants gives `y(θ) = W(θ) (y(0) + ∫₀^θ W(s)^* f(s) ds)`.

For the paper's forcing `f = -(i/√2) g e₀` this yields Lemma 4.10:
* `√2 ⟨e₀, y(θ)⟩ = √2 (O_E v)(θ) - i (T_E g)(θ)` (the trace identity `h_a = √2 O_E v - i T_E g`),
* if moreover `y(L) = y(0) = v`, then `(I - V_E) v = -(i/√2) V_E O_E^* g` and
  `O_E^* g = √2 i (V_E^* - I) v`,

where `(O_E v)(θ) = ⟨e₀, W(θ) v⟩`, `(T_E g)(θ) = ∫₀^θ ⟨e₀, W(θ) W(s)^* e₀⟩ g(s) ds` and
`O_E^* g = ∫₀^L g(s) W(s)^* e₀ ds`.  We also prove the adjoint formula for `O_E^*` and the
kernel identity `T_E + T_E^* = O_E O_E^*` of Lemma 4.6.
-/
@[expose] public section
open MeasureTheory Set Filter
open scoped ComplexConjugate Real
noncomputable section
namespace PolyaNeumann
instance instStarModuleRealCLMComplex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : StarModule ℝ (E →L[ℂ] E) :=
  ⟨fun r A => by
    have h : ∀ B : E →L[ℂ] E, r • B = (r : ℂ) • B := fun B =>
      RCLike.real_smul_eq_coe_smul (K := ℂ) r B
    rw [star_trivial r, h, h, star_smul, Complex.star_def, Complex.conj_ofReal]⟩
end PolyaNeumann
end
