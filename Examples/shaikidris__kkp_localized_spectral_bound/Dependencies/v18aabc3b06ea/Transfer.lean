/-
Local exploratory transfer, generated with Codex on 2026-10-13.
Imports the Apache-2.0 BN development by Shengtong Zhang and collaborators.
Upstream source is unmodified; see ../upstream/LICENSE and the upstream metadata ../upstream/formalization.yaml.
-/
module
public import Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.Spectral.Weighted
@[expose] public section
/-! A general scalar-certificate transfer. The certificate is an explicit premise;
this module does not yet formalize Bradač's edge-clique producer. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix BN
open scoped Matrix
namespace LocalBN
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- Factorwise passage of a homogeneous scalar certificate to CP matrices. -/
theorem cpPairing {W C : Matrix n n ℝ}
    (hscalar : ∀ y : n → ℝ, (∀ i, 0 ≤ y i) →
      BN.inner W (vecMulVec y y) ≤ (∑ i, y i) ^ 2)
    (hC : IsCompletelyPositive C) :
    BN.inner W C ≤ BN.inner (of fun _ _ => (1 : ℝ)) C := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  rw [BN.inner_sum Finset.univ W (fun a => vecMulVec (p a) (p a))]
  rw [BN.inner_sum Finset.univ (of fun _ _ => (1 : ℝ))
    (fun a => vecMulVec (p a) (p a))]
  simp_rw [BN.inner_one_vecMulVec]
  exact Finset.sum_le_sum fun a _ => hscalar (p a) (hp a)
end LocalBN
