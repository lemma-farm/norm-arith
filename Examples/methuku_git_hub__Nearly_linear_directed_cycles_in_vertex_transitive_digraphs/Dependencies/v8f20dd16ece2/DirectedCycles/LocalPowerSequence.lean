module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalGroupProducts
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
/-- A sequence of powers whose every finite product, with every bracketing,
is actually defined. This is stronger than a left-associated recursion. -/
structure PowerSequence (g : G) where
  power : ℕ → G
  product : ∀ n, L.Product (List.replicate n g) (power n)
namespace PowerSequence
variable {L} {g : G} (p : L.PowerSequence g)
theorem one : p.power 1 = g := (Product.singleton_iff L).1 (p.product 1)
end PowerSequence
end LocalGroupAlgebra
end DirectedCycles
