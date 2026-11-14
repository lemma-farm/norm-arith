module

public import Mathlib.Tactic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.Normed.Module.Basic

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalGroupAlgebra ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
/-- Algebraic part of a symmetric local group. Multiplication is a functional
relation so that undefined products cannot accidentally be used as elements.
Associativity applies only when both bracketings are defined. -/
structure LocalGroupAlgebra (G : Type*) where
  one : G
  inv : G → G
  mulRel : G → G → G → Prop
  unique : ∀ {a b c d}, mulRel a b c → mulRel a b d → c = d
  one_mul : ∀ a, mulRel one a a
  mul_one : ∀ a, mulRel a one a
  inv_mul : ∀ a, mulRel (inv a) a one
  mul_inv : ∀ a, mulRel a (inv a) one
  assoc : ∀ {a b c ab bc x y}, mulRel a b ab → mulRel b c bc →
    mulRel ab c x → mulRel a bc y → x = y
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

end LocalGroupAlgebra
end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalGroupProducts ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
/-- A local finite product requires valid products for every contiguous split,
recursively, and the same value at each split. This does not identify arbitrary
bracketings merely because a left-associated computation happens to exist. -/
inductive Product : List G → G → Prop
  | nil : Product [] L.one
  | singleton (a : G) : Product [a] a
  | splits {l : List G} {x : G} (hlen : 2 ≤ l.length)
      (u v : List G → List G → G)
      (left : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] → Product a (u a b))
      (right : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] → Product b (v a b))
      (multiply : ∀ a b : List G, l = a++b → a ≠ [] → b ≠ [] → L.mulRel (u a b) (v a b) x) : Product l x

end LocalGroupAlgebra
end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalFiniteTranslations ====
public section
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

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalUltraproductDomain ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
variable {ι : Type*} (F : Filter ι) (G : ι → Type*) (L : ∀ i, LocalGroupAlgebra (G i))
def LocalGroupAlgebra.setMul {X : Type*} (L : LocalGroupAlgebra X) (A B : Set X) : Set X :=
  {z | ∃ a ∈ A, ∃ b ∈ B, L.mulRel a b z}
end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalWordPowers ====
public section
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

end LocalGroupAlgebra
end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalFiniteConvolution ====
public section
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)

section Finite
variable [Fintype G]
/-- Finite convolution uses the actual partial product and zero outside its
domain, through the already-defined partial left translations. -/
noncomputable def convolution (f k : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y*L.leftShift y k x

end Finite
end LocalGroupAlgebra
end DirectedCycles

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalApproximateGroups ====
public section
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

end
end

-- ==== Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Examples.Example_6f443b36828409e86eab_LocalNormalizedConvolution ====
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
section Finite
variable [Fintype G]
noncomputable def normalizedConvolution (A : Finset G) (f k : G → ℝ) : G → ℝ :=
  ((A.card : ℝ)⁻¹) • L.convolution f k
set_option linter.unusedVariables false in
axiom _root_.DirectedCycles.LocalGroupAlgebra.norm_convolution_le_card.{w_u_1} : ∀ {G : Type w_u_1} (L : DirectedCycles.LocalGroupAlgebra G) [inst : Fintype G] (A : Finset G)
  {f k : G → ℝ},
  (∀ (x : G), 0 ≤ f x ∧ f x ≤ 1) →
    (∀ (x : G), 0 ≤ k x ∧ k x ≤ 1) → (∀ x ∉ A, f x = 0) → ‖L.convolution f k‖ ≤ (↑A.card : ℝ)
set_option linter.unusedVariables false in
theorem norm_normalizedConvolution_le {A : Finset G} {K : ℕ}
    (hA : IsLocalFiniteApproximateGroup L K A) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hs : ∀ x, x ∉ L.wordPower (A : Set G) 2 → f x = 0) 
    (h_DirectedCycles_local_approximate_doubling : ∀ {G : Type u_1} [Fintype G] {L : DirectedCycles.LocalGroupAlgebra G} {K : ℕ} {A : Finset G},
      DirectedCycles.IsLocalFiniteApproximateGroup L K A →
        Nat.card (↑(L.wordPower (↑A : Set G) 2) : Type u_1) ≤ K * A.card)
    :
    ‖L.normalizedConvolution A f k‖ ≤ K := by
  classical
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  let B := (L.wordPower (A : Set G) 2).toFinset
  have hBcard : B.card = Nat.card (L.wordPower (A : Set G) 2) := by
    rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  have hcard : (B.card : ℝ) ≤ (K : ℝ)*A.card := by
    exact_mod_cast (hBcard ▸ h_DirectedCycles_local_approximate_doubling hA)
  have hsB : ∀ x, x ∉ B → f x = 0 := by
    intro x hx
    apply hs
    simpa only [B,Set.mem_toFinset] using hx
  unfold normalizedConvolution
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
  calc
    (A.card : ℝ)⁻¹*‖L.convolution f k‖ ≤ (A.card : ℝ)⁻¹*B.card :=
      mul_le_mul_of_nonneg_left (L.norm_convolution_le_card B hf hk hsB) (by positivity)
    _ ≤ (A.card : ℝ)⁻¹*((K : ℝ)*A.card) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = K := by field_simp
end Finite
end LocalGroupAlgebra
end DirectedCycles
