module

public import Mathlib

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vee81fbcd2d51.DedekindZetaZeroFree.Arithmetic.RayClasses.Character ====
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical
structure RayClassCharacter (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) where
  toFun : Ideal (𝓞 F) → ℂ
  map_mul' : ∀ I J, toFun (I * J) = toFun I * toFun J
  map_top' : toFun ⊤ = 1
  eq_zero_iff' : ∀ I, toFun I = 0 ↔ (I = ⊥ ∨ I ⊔ 𝔪 ≠ ⊤)
  map_span' : ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 → (∀ φ : F →+* ℝ, 0 < φ (α : F)) →
    toFun (Ideal.span {α}) = 1
instance (F : Type) [Field F] [NumberField F] (𝔪 : Ideal (𝓞 F)) :
    CoeFun (RayClassCharacter F 𝔪) (fun _ => Ideal (𝓞 F) → ℂ) :=
  ⟨RayClassCharacter.toFun⟩
def RayClassCharacter.IsPrimitive {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
    (η : RayClassCharacter F 𝔪) : Prop :=
  ∀ 𝔣 : Ideal (𝓞 F), 𝔪 < 𝔣 → ∃ α : 𝓞 F, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧ (∀ φ : F →+* ℝ, 0 < φ (α : F)) ∧
    Ideal.span {α} ⊔ 𝔪 = ⊤ ∧ η (Ideal.span {α}) ≠ 1
structure QuadraticHeckeFamily (F : Type) [Field F] [NumberField F] (𝔠 : Ideal (𝓞 F)) where
  cond : Ideal (𝓞 F) → Ideal (𝓞 F)
  χ : (𝔞 : Ideal (𝓞 F)) → RayClassCharacter F (cond 𝔞)
  primitive : ∀ 𝔞, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → cond 𝔞 ≠ ⊥ ∧ (χ 𝔞).IsPrimitive
  quadratic : ∀ 𝔞 𝔟, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → (χ 𝔞) 𝔟 ^ 3 = (χ 𝔞) 𝔟
  G : Type
  instGroup : Group G
  instFinite : Finite G
  cls : Ideal (𝓞 F) → G
  cls_top : cls ⊤ = 1
  cls_mul : ∀ 𝔞 𝔟, 𝔞 ⊔ 𝔠 = ⊤ → 𝔟 ⊔ 𝔠 = ⊤ → cls (𝔞 * 𝔟) = cls 𝔞 * cls 𝔟
  C : G → G → ℂ
  C_sq : ∀ g h, C g h ^ 2 = 1
  reciprocity : ∀ 𝔞 𝔟, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → Squarefree 𝔟 → 𝔟 ⊔ 𝔠 = ⊤ → 𝔞 ⊔ 𝔟 = ⊤ →
    (χ 𝔞) 𝔟 = (χ 𝔟) 𝔞 * C (cls 𝔞) (cls 𝔟)
  product_primitive : ∀ 𝔞 𝔟, Squarefree 𝔞 → 𝔞 ⊔ 𝔠 = ⊤ → Squarefree 𝔟 → 𝔟 ⊔ 𝔠 = ⊤ →
    𝔞 ⊔ 𝔟 = ⊤ → cls 𝔞 = cls 𝔟 →
    ∃ ψ : RayClassCharacter F (𝔞 * 𝔟), ψ.IsPrimitive ∧
      ∀ 𝔫, 𝔫 ⊔ (cond 𝔞 * cond 𝔟) = ⊤ → ψ 𝔫 = (χ 𝔞) 𝔫 * (starRingEnd ℂ) ((χ 𝔟) 𝔫)
end
end DedekindZetaZeroFree

end
end

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.vee81fbcd2d51.DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.CharacterValues ====
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)} (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
variable {a : Ideal (𝓞 F)}

axiom quadraticFamily_norm_le_one
    (ha : Squarefree a) (hac : a ⊔ c = ⊤) (n : Ideal (𝓞 F)) :
    ‖(Q.χ a) n‖ ≤ 1
end DedekindZetaZeroFree.LargeSieve

end
end

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Examples.Example_19bdeebcffdee8402d57_DyadicUnitBlockBounds ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve.Sieve
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
private axiom squarefree_top_ideal : Squarefree (⊤ : Ideal (𝓞 F))
private theorem unit_column_bound (c : Ideal (𝓞 F))
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (S : Finset (Ideal (𝓞 F)))
    (lam : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ S, ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2) ≤
      (S.card : ℝ) * ‖lam ⊤‖ ^ 2 := by
  have hbound : ∀ a ∈ S,
      ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2 ≤ ‖lam ⊤‖ ^ 2 := by
    intro a _
    rw [Finset.sum_singleton, norm_mul, mul_pow]
    have h1 : ‖(Q.χ ⊤) a‖ ^ 2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (quadraticFamily_norm_le_one Q squarefree_top_ideal (by simp) a)
    calc ‖lam ⊤‖ ^ 2 * ‖(Q.χ ⊤) a‖ ^ 2 ≤ ‖lam ⊤‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = ‖lam ⊤‖ ^ 2 := mul_one _
  calc (∑ a ∈ S, ‖∑ _b ∈ ({⊤} : Finset (Ideal (𝓞 F))), lam _b * (Q.χ _b) a‖ ^ 2)
      ≤ ∑ _a ∈ S, ‖lam ⊤‖ ^ 2 := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) * ‖lam ⊤‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
end DedekindZetaZeroFree.LargeSieve.Sieve
