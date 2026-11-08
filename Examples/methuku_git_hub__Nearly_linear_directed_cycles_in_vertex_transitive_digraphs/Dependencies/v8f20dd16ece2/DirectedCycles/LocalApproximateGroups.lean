module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalWordPowerMaps
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*}
/-- BGT's finite local approximate group, including the 200-letter domain
condition and the symmetric covering set inside the third word power. -/
structure IsLocalFiniteApproximateGroup (L : LocalGroupAlgebra G) (K : ℕ) (A : Finset G) : Prop where
  one_le : 1 ≤ K
  one_mem : L.one ∈ A
  inv_mem : ∀ a ∈ A, L.inv a ∈ A
  allProducts : L.AllProductsDefined (A : Set G) 200
  cover : ∃ X : Finset G, X.card ≤ K ∧ (∀ x ∈ X, L.inv x ∈ X) ∧
    (X : Set G) ⊆ L.wordPower (A : Set G) 3 ∧
    L.wordPower (A : Set G) 2 ⊆ L.setMul (X : Set G) (A : Set G)
namespace IsLocalFiniteApproximateGroup
variable {H : Type*} [DecidableEq H] {L : LocalGroupAlgebra G} {M : LocalGroupAlgebra H}
    {K : ℕ} {A : Finset G}
end IsLocalFiniteApproximateGroup
end DirectedCycles
