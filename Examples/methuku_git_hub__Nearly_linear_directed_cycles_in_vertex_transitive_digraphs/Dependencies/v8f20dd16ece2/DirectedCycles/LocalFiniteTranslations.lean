module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalDivision
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.FiniteGroupDerivatives
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
/-- Translation by a local group element, extended by zero outside its actual
range. No arbitrary multiplication is introduced at undefined pairs. -/
noncomputable def leftShift (g : G) (f : G → ℝ) (x : G) : ℝ := by
  classical
  exact if h : ∃ y, L.mulRel g y x then f (Classical.choose h) else 0
section Finite
variable [Fintype G]
end Finite
end LocalGroupAlgebra
end DirectedCycles
