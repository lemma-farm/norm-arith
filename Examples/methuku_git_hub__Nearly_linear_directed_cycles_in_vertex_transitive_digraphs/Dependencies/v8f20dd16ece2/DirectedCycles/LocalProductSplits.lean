module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalGroupProducts
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
/-- Existential split witnesses are safe as a theorem, while the inductive
constructor retains its explicit function witnesses for kernel recursion. -/
theorem Product.of_splits {l : List G} {x : G} (hlen : 2 ≤ l.length)
    (h : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] →
      ∃ u v : G, L.Product a u ∧ L.Product b v ∧ L.mulRel u v x) : L.Product l x := by
  classical
  have hc : ∀ a b : List G, ∃ u v : G, l = a++b → a ≠ [] → b ≠ [] →
      L.Product a u ∧ L.Product b v ∧ L.mulRel u v x := by
    intro a b
    by_cases he : l = a++b ∧ a ≠ [] ∧ b ≠ []
    · obtain ⟨u,v,hu,hv,hm⟩ := h a b he.1 he.2.1 he.2.2
      exact ⟨u,v,fun _ _ _ => ⟨hu,hv,hm⟩⟩
    · exact ⟨L.one,L.one,fun h1 h2 h3 => (he ⟨h1,h2,h3⟩).elim⟩
  choose u v huv using hc
  exact Product.splits hlen u v (fun a b he ha hb => (huv a b he ha hb).1)
    (fun a b he ha hb => (huv a b he ha hb).2.1)
    (fun a b he ha hb => (huv a b he ha hb).2.2)
end LocalGroupAlgebra
end DirectedCycles
