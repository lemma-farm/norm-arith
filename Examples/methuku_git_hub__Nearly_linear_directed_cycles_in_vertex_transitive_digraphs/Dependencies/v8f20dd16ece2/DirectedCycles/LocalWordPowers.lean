module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalProductInversion
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalUltraproductDomain
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
/-- Values of fully defined words of exactly n letters from A. -/
def wordPower (A : Set G) (n : ℕ) : Set G :=
  {x | ∃ l : List G, l.length = n ∧ (∀ a ∈ l, a ∈ A) ∧ L.Product l x}
/-- Every word of length at most N in A has all bracketings defined. -/
def AllProductsDefined (A : Set G) (N : ℕ) : Prop :=
  ∀ l : List G, l.length ≤ N → (∀ a ∈ l, a ∈ A) → ∃ x, L.Product l x
theorem Product.split_allow_empty {l a b : List G} {x : G} (h : L.Product l x)
    (he : l = a++b) : ∃ u v : G, L.Product a u ∧ L.Product b v ∧ L.mulRel u v x := by
  by_cases ha : a = []
  · subst a
    simp only [List.nil_append] at he
    exact ⟨L.one,x,Product.nil,he ▸ h,L.one_mul x⟩
  by_cases hb : b = []
  · subst b
    simp only [List.append_nil] at he
    exact ⟨x,L.one,he ▸ h,Product.nil,L.mul_one x⟩
  exact h.split L he ha hb
end LocalGroupAlgebra
end DirectedCycles
