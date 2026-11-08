module
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalConvolutionNorm
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.LocalApproximateCube
public import Examples.methuku_git_hub__Nearly_linear_directed_cycles_in_vertex_transitive_digraphs.Dependencies.v8f20dd16ece2.DirectedCycles.FiniteConvolutionBounds
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
theorem norm_convolution_le_card (A : Finset G) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hs : ∀ x, x ∉ A → f x = 0) : ‖L.convolution f k‖ ≤ A.card := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).2
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (L.convolution_nonneg (fun x => (hf x).1) (fun x => (hk x).1) x)]
  exact L.convolution_le_card A hf hk hs x
theorem norm_normalizedConvolution_le {A : Finset G} {K : ℕ}
    (hA : IsLocalFiniteApproximateGroup L K A) {f k : G → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hk : ∀ x, 0 ≤ k x ∧ k x ≤ 1)
    (hs : ∀ x, x ∉ L.wordPower (A : Set G) 2 → f x = 0) :
    ‖L.normalizedConvolution A f k‖ ≤ K := by
  classical
  have ha : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨L.one,hA.one_mem⟩
  let B := (L.wordPower (A : Set G) 2).toFinset
  have hBcard : B.card = Nat.card (L.wordPower (A : Set G) 2) := by
    rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card']
  have hcard : (B.card : ℝ) ≤ (K : ℝ)*A.card := by
    exact_mod_cast (hBcard ▸ local_approximate_doubling hA)
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
