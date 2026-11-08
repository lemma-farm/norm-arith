module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalFiniteTranslations
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.FiniteGroupConvolution
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalWordPowers
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
namespace DirectedCycles
namespace LocalGroupAlgebra
variable {G : Type*} (L : LocalGroupAlgebra G)
/-- Scalar bounds survive zero-extended local translation. -/
theorem leftShift_nonneg {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) (g x : G) :
    0 ≤ L.leftShift g f x := by
  classical
  unfold leftShift
  split_ifs
  · exact hf _
  · exact le_rfl
theorem leftShift_le_one {f : G → ℝ} (hf : ∀ x, f x ≤ 1) (g x : G) :
    L.leftShift g f x ≤ 1 := by
  classical
  unfold leftShift
  split_ifs
  · exact hf _
  · norm_num
section Finite
variable [Fintype G]
/-- Finite convolution uses the actual partial product and zero outside its
domain, through the already-defined partial left translations. -/
noncomputable def convolution (f k : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y*L.leftShift y k x
theorem convolution_nonneg {f k : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hk : ∀ x, 0 ≤ k x) (x : G) :
    0 ≤ L.convolution f k x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hf y) (L.leftShift_nonneg hk y x)
theorem convolution_eq_sum_support {f k : G → ℝ} (A : Finset G)
    (hf : ∀ y, y ∉ A → f y = 0) (x : G) :
    L.convolution f k x = ∑ y ∈ A, f y*L.leftShift y k x := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ A)
  intro y _ hy
  rw [hf y hy,zero_mul]
theorem convolution_le_card {f k : G → ℝ} (A : Finset G)
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) (hk : ∀ y, 0 ≤ k y ∧ k y ≤ 1)
    (hs : ∀ y, y ∉ A → f y = 0) (x : G) :
    L.convolution f k x ≤ A.card := by
  rw [L.convolution_eq_sum_support A hs]
  calc
    ∑ y ∈ A, f y*L.leftShift y k x ≤ ∑ _y ∈ A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y _
      have hlo := L.leftShift_nonneg (fun z => (hk z).1) y x
      have hhi := L.leftShift_le_one (fun z => (hk z).2) y x
      nlinarith [(hf y).1,(hf y).2]
    _ = A.card := by simp
end Finite
end LocalGroupAlgebra
end DirectedCycles
