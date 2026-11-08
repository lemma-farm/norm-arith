module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalGroupHom
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalPowerSequence
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
/-- A genuine global subgroup inside a local group: its multiplication is total
on the subset, and the subset contains the identity and all inverses. -/
structure IsGlobalSubgroup (S : Set G) : Prop where
  one_mem : L.one ∈ S
  inv_mem : ∀ x ∈ S, L.inv x ∈ S
  mul_total : ∀ x ∈ S, ∀ y ∈ S, ∃ z ∈ S, L.mulRel x y z
namespace IsGlobalSubgroup
variable {L} {S : Set G} (hS : L.IsGlobalSubgroup S)
end IsGlobalSubgroup
end LocalGroupAlgebra
end DirectedCycles
