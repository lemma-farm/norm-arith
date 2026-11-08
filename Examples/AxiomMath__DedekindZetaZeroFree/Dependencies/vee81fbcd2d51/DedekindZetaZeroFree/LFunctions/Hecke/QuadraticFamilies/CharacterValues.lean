module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vee81fbcd2d51.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
variable {a : Ideal (𝓞 F)}
private lemma mem_zero_one_neg_one_of_cube_eq_self {z : ℂ} (h : z ^ 3 = z) :
    z ∈ ({0, 1, -1} : Set ℂ) := by
  have hfac : z * (z - 1) * (z + 1) = z ^ 3 - z := by ring
  have hzero : z * (z - 1) * (z + 1) = 0 := by rw [hfac, sub_eq_zero.mpr h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases mul_eq_zero.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (add_eq_zero_iff_eq_neg.mp h))
theorem quadraticFamily_mem_zero_one_neg_one
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F)) :
    (Q.χ a) n ∈ ({0, 1, -1} : Set ℂ) :=
  mem_zero_one_neg_one_of_cube_eq_self (Q.quadratic a n ha hac)
theorem quadraticFamily_norm_le_one
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F)) :
    ‖(Q.χ a) n‖ ≤ 1 := by
  have hmem := quadraticFamily_mem_zero_one_neg_one Q ha hac n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h <;> rw [h] <;> norm_num
end DedekindZetaZeroFree.LargeSieve
