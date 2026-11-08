module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalGroupUltraproduct
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
def LocalGroupAlgebra.setMul {X : Type*} (L : LocalGroupAlgebra X) (A B : Set X) : Set X :=
  {z | ∃ a ∈ A, ∃ b ∈ B, L.mulRel a b z}
end DirectedCycles
