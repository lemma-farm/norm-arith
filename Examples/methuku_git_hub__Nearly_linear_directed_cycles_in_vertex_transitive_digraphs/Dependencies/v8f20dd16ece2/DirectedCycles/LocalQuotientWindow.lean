module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalGroupAlgebra
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
open scoped Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G]
/-- Conditions sufficient for quotienting inside a small window. The set P may
extend beyond V; closure and conjugation are required whenever the result lies
in V. The quotient proofs below do not require P to be a global subgroup. -/
structure LocalNormalSet (P V : Set G) : Prop where
  one_mem : (1 : G) ∈ P
  inv_mem : ∀ x ∈ P, x⁻¹ ∈ P
  mul_mem : ∀ x ∈ P, ∀ y ∈ P, x*y ∈ V → x*y ∈ P
  conj_mem : ∀ x ∈ V, ∀ p ∈ P, x*p*x⁻¹ ∈ V → x*p*x⁻¹ ∈ P
namespace LocalNormalSet
variable {P V W : Set G} (hP : LocalNormalSet P V)
    (hW1 : (1 : G) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)
end LocalNormalSet
end DirectedCycles
