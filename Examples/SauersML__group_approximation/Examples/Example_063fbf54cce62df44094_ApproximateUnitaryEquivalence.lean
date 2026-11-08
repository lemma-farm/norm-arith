import Examples.SauersML__group_approximation.Dependencies.vc4a590b63a62.GroupApproximation.KirchbergPhillips.IntertwiningLimit
import Mathlib.Algebra.Star.UnitaryStarAlgAut
set_option warningAsError true
/-!
# Approximate unitary equivalence and Elliott's intertwining theorem

Two unital ⋆-homomorphisms `ρ σ : A →⋆ₐ[ℂ] B` are approximately unitarily equivalent when every
finite set is moved within any `ε` of `σ` by conjugating `ρ` with a unitary of `B`.

**Elliott's intertwining theorem.** Let `A` and `B` be separable unital C⋆-algebras. If
`ρ : A → B` and `σ : B → A` are unital ⋆-homomorphisms with `σ ∘ ρ ≈ᵤ id` and `ρ ∘ σ ≈ᵤ id`, then
`A ≃⋆ₐ[ℂ] B` (`nonempty_starAlgEquiv_of_approxUnitarilyEquivalent`).

The proof builds `α n = Ad uₙ ∘ ρ` and `β n = Ad vₙ ∘ σ` with finite sets `F n ⊆ A`, `G n ⊆ B` and
errors `2⁻ⁿ` (`exists_intertwining_data`), then passes to the limit with
`nonempty_starAlgEquiv_of_tendsto`.

## Main definitions

* `conjHom u ρ`: `x ↦ u ρ(x) u⋆`.
* `ApproxUnitarilyEquivalent ρ σ`.
-/
open Filter Topology TopologicalSpace
namespace GroupApproximation
namespace KirchbergPhillips
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
def ApproxUnitarilyEquivalent (ρ σ : A →⋆ₐ[ℂ] B) : Prop :=
  ∀ F : Finset A, ∀ ε : ℝ, 0 < ε →
    ∃ u : unitary B, ∀ x ∈ F, ‖(u : B) * ρ x * star (u : B) - σ x‖ < ε
theorem ApproxUnitarilyEquivalent.symm {ρ σ : A →⋆ₐ[ℂ] B} (h : ApproxUnitarilyEquivalent ρ σ) :
    ApproxUnitarilyEquivalent σ ρ := by
  intro F ε hε
  obtain ⟨u, hu⟩ := h F ε hε
  refine ⟨star u, fun x hx => ?_⟩
  have key : ((star u : unitary B) : B) * σ x * star ((star u : unitary B) : B) - ρ x =
      star (u : B) * (σ x - (u : B) * ρ x * star (u : B)) * (u : B) := by
    simp only [Unitary.coe_star, star_star, mul_sub, sub_mul, mul_assoc]
    simp only [← mul_assoc (star (u : B)) (u : B), Unitary.star_mul_self_of_mem u.2, one_mul,
      mul_one]
  rw [key, CStarRing.norm_mul_coe_unitary, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem u.2),
    norm_sub_rev]
  exact hu x hx
end KirchbergPhillips
end GroupApproximation
