module

public import Mathlib

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v7541bf954a90.DedekindZetaZeroFree.Arithmetic.RayClasses.Character ====
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

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v7541bf954a90.DedekindZetaZeroFree.Arithmetic.Ideals.BoundedNormFinsets ====
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve
open scoped NumberField Classical
set_option linter.unusedVariables false in
axiom _root_.DedekindZetaZeroFree.LargeSieve.finite_ideals_absNorm_le.{w_u_1} : ∀ (F : Type w_u_1) [inst : Field F] [inst_1 : NumberField F] (X : ℝ),
  {I : Ideal (NumberField.RingOfIntegers F) |
      (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers F) → ℕ) I) : ℝ) ≤ X}.Finite
noncomputable def boundedNormIdeals (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Finset (Ideal (𝓞 F)) :=
  (finite_ideals_absNorm_le F X).toFinset
end DedekindZetaZeroFree.LargeSieve

end
end

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v7541bf954a90.DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleIdealRanges ====
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve.Sieve
open scoped NumberField Classical
noncomputable def idealAdmissibleFinset (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (X : ℝ) : Finset (Ideal (𝓞 F)) :=
  (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).filter (fun I => Squarefree I ∧ I ⊔ c = ⊤)
noncomputable def paperShell (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (T : ℝ) : Finset (Ideal (𝓞 F)) :=
  (idealAdmissibleFinset F c (2 * T)).filter (fun I => T < (Ideal.absNorm I : ℝ))
end DedekindZetaZeroFree.LargeSieve.Sieve

end
end

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v7541bf954a90.DedekindZetaZeroFree.Arithmetic.Ideals.DyadicNormBlocks ====
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve.Sieve
open scoped NumberField Classical
noncomputable def idealDyadicBlock (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) : ℕ → Finset (Ideal (𝓞 F))
  | 0 => {⊤}
  | k + 1 => paperShell F c ((2 : ℝ) ^ k)
def dyadicScale : ℕ → ℝ
  | 0 => 1
  | k + 1 => (2 : ℝ) ^ k
end DedekindZetaZeroFree.LargeSieve.Sieve

end
end

-- ==== Examples.AxiomMath__DedekindZetaZeroFree.Examples.Example_c2d3702a3701e4480e2e_DyadicUnitBlockBounds ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.LargeSieve.Sieve
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]


set_option linter.unusedVariables false in
theorem unit_block_extension
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (𝓕 : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ) (hC : 0 ≤ C) (A : ℝ) (hA : 1 ≤ A)
    (hcount : ∀ X : ℝ, 1 ≤ X →
      ((DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X)
    (hshell : ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ lam : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ paperShell F c M,
        ‖∑ b ∈ paperShell F c N, lam b * (𝓕.χ b) a‖ ^ 2) ≤
      C * (M * N) ^ δ * (M + N) *
        ∑ b ∈ paperShell F c N, ‖lam b‖ ^ 2) 
    (h_DedekindZetaZeroFree_LargeSieve_Sieve_unit_row_bound : ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (c : Ideal (NumberField.RingOfIntegers F))
      (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
      (S : Finset (Ideal (NumberField.RingOfIntegers F)))
      (lam : Ideal (NumberField.RingOfIntegers F) → ℂ),
      ∑ _a ∈ {⊤}, ‖∑ b ∈ S, lam b * (Q.χ b).toFun _a‖ ^ 2 ≤ (↑S.card : ℝ) * ∑ b ∈ S, ‖lam b‖ ^ 2)
    (h_DedekindZetaZeroFree_LargeSieve_Sieve_shell_constant_le : ∀ (C A δ m n E : ℝ),
      0 ≤ C →
        1 ≤ A →
          0 ≤ δ →
            1 ≤ m →
              1 ≤ n →
                0 ≤ E → C * (m * n) ^ δ * (m + n) * E ≤ (C + 2 * A + 1) * (m * n) ^ δ * (m + n) * E)
    (h_DedekindZetaZeroFree_LargeSieve_Sieve_both_unit_arith : ∀ (C A δ E : ℝ), 0 ≤ C → 1 ≤ A → 0 ≤ E → E ≤ (C + 2 * A + 1) * (1 * 1) ^ δ * (1 + 1) * E)
    (h_DedekindZetaZeroFree_LargeSieve_Sieve_unit_error_factor : ∀ (C A δ s t : ℝ),
      0 ≤ C → 1 ≤ A → 0 ≤ δ → 1 ≤ s → 1 ≤ t → A * (2 * s) ≤ (C + 2 * A + 1) * (s * t) ^ δ * (s + t))
    (h_DedekindZetaZeroFree_LargeSieve_Sieve_dyadicBlock_card_le : ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (c : Ideal (NumberField.RingOfIntegers F))
      (A : ℝ),
      1 ≤ A →
        (∀ (X : ℝ),
            1 ≤ X → (↑(DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F X).card : ℝ) ≤ A * X) →
          ∀ (j : ℕ),
            (↑(DedekindZetaZeroFree.LargeSieve.Sieve.idealDyadicBlock F c j).card : ℝ) ≤
              A * (2 * DedekindZetaZeroFree.LargeSieve.Sieve.dyadicScale j))
    (h_DedekindZetaZeroFree_LargeSieve_Sieve_unit_column_bound : ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (c : Ideal (NumberField.RingOfIntegers F))
      (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
      (S : Finset (Ideal (NumberField.RingOfIntegers F)))
      (lam : Ideal (NumberField.RingOfIntegers F) → ℂ),
      ∑ a ∈ S, ‖∑ _b ∈ {⊤}, lam _b * (Q.χ _b).toFun a‖ ^ 2 ≤ (↑S.card : ℝ) * ‖lam ⊤‖ ^ 2)
    :
    ∀ i j : ℕ, ∀ lam : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ idealDyadicBlock F c i,
        ‖∑ b ∈ idealDyadicBlock F c j, lam b * (𝓕.χ b) a‖ ^ 2) ≤
      (C + 2 * A + 1) * (dyadicScale i * dyadicScale j) ^ δ *
        (dyadicScale i + dyadicScale j) *
        ∑ b ∈ idealDyadicBlock F c j, ‖lam b‖ ^ 2 := by
  intro i j lam
  rcases i with _ | k
  · rcases j with _ | l
    ·
      simp only [idealDyadicBlock, dyadicScale, Finset.sum_singleton]
      rw [show (𝓕.χ ⊤) ⊤ = 1 from (𝓕.χ ⊤).map_top', mul_one]
      exact h_DedekindZetaZeroFree_LargeSieve_Sieve_both_unit_arith C A δ _ hC hA (sq_nonneg _)
    ·
      simp only [idealDyadicBlock, dyadicScale]
      have hE : 0 ≤ ∑ b ∈ paperShell F c ((2 : ℝ) ^ l), ‖lam b‖ ^ 2 :=
        Finset.sum_nonneg (fun b _ => sq_nonneg _)
      have hcard := h_DedekindZetaZeroFree_LargeSieve_Sieve_dyadicBlock_card_le c A hA hcount (l + 1)
      simp only [idealDyadicBlock, dyadicScale] at hcard
      have hfac := h_DedekindZetaZeroFree_LargeSieve_Sieve_unit_error_factor C A δ ((2 : ℝ) ^ l) 1 hC hA hδ
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)
      refine le_trans (h_DedekindZetaZeroFree_LargeSieve_Sieve_unit_row_bound c 𝓕 (paperShell F c ((2 : ℝ) ^ l)) lam) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hcard hE) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hfac hE) ?_
      exact le_of_eq (by rw [mul_one, one_mul, add_comm (1 : ℝ) ((2 : ℝ) ^ l)])
  · rcases j with _ | l
    ·
      simp only [idealDyadicBlock, dyadicScale]
      have hE : 0 ≤ ‖lam ⊤‖ ^ 2 := sq_nonneg _
      have hcard := h_DedekindZetaZeroFree_LargeSieve_Sieve_dyadicBlock_card_le c A hA hcount (k + 1)
      simp only [idealDyadicBlock, dyadicScale] at hcard
      have hfac := h_DedekindZetaZeroFree_LargeSieve_Sieve_unit_error_factor C A δ ((2 : ℝ) ^ k) 1 hC hA hδ
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num)
      refine le_trans (h_DedekindZetaZeroFree_LargeSieve_Sieve_unit_column_bound c 𝓕 (paperShell F c ((2 : ℝ) ^ k)) lam) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hcard hE) ?_
      refine le_trans (mul_le_mul_of_nonneg_right hfac hE) ?_
      exact le_of_eq (by rw [Finset.sum_singleton])
    ·
      simp only [idealDyadicBlock, dyadicScale, one_mul, mul_one]
      refine le_trans (hshell ((2 : ℝ) ^ k) ((2 : ℝ) ^ l)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) lam) ?_
      exact h_DedekindZetaZeroFree_LargeSieve_Sieve_shell_constant_le C A δ ((2 : ℝ) ^ k) ((2 : ℝ) ^ l) _
        hC hA hδ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (Finset.sum_nonneg (fun b _ => sq_nonneg _))
end DedekindZetaZeroFree.LargeSieve.Sieve
