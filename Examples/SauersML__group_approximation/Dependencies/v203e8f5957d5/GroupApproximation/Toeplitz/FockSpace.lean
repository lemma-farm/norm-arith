/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError true
/-!
# Creation and annihilation operators on a full Fock space

For an index type `ι`, `Fib ι = ℓ²(ι)` and `Fock ι = ℓ²(List ι)`, the full Fock space
`⊕_m ℓ²(ι)^{⊗m}`: a word of length `m` indexes a basis vector of the `m`-th tensor power.
The creation operator `creation a` sends `ω` to `a ⊗ ω`, with coordinates `tensorCoord a ω`.
The main facts are `⟪a ⊗ ω, b ⊗ ω'⟫ = ⟪a, b⟫ ⟪ω, ω'⟫` (`inner_creation`) and, for the adjoint
`annihilation a`, `annihilation a (b ⊗ ω) = ⟪a, b⟫ ω` (`annihilation_creation`).

These operators are the fibres of the creation operators of Blanchard, arXiv:1507.02535v1,
Definition 5.1 (p. 7); see `Palomar/BlanchardToeplitzChallenge.lean`.
-/
namespace GroupApproximation.Toeplitz
noncomputable section
open scoped ENNReal InnerProductSpace ComplexConjugate InnerProduct
variable {ι : Type*}
/-- The Hilbert space `ℓ²(ι)`. -/
abbrev Fib (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2
/-- The full Fock space `ℓ²(List ι)`. -/
abbrev Fock (ι : Type*) : Type _ := lp (fun _ : List ι => ℂ) 2
/-- The coordinates of `ζ ⊗ ω`. -/
def tensorCoord (ζ : ι → ℂ) (ω : List ι → ℂ) : List ι → ℂ
  | [] => 0
  | i :: w => ζ i * ω w
theorem holderConjugate_two_two :
    (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
  rw [Real.holderConjugate_iff]; norm_num
theorem summable_norm_mul_norm {α : Type*} (f g : lp (fun _ : α => ℂ) 2) :
    Summable fun i => ‖f i‖ * ‖g i‖ :=
  lp.summable_mul holderConjugate_two_two f g
theorem summable_norm_inner {α : Type*} (f g : lp (fun _ : α => ℂ) 2) :
    Summable fun i => ‖⟪f i, g i⟫_ℂ‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_inner_le_norm (𝕜 := ℂ) _ _)
    (summable_norm_mul_norm f g)
theorem cons_injective : Function.Injective fun p : ι × List ι => p.1 :: p.2 :=
  fun _ _ h => Prod.ext (List.cons.inj h).1 (List.cons.inj h).2
theorem memℓp_tensorCoord (a : Fib ι) (ω : Fock ι) : Memℓp (tensorCoord a ω) 2 := by
  refine memℓp_gen ?_
  have hpow : ∀ z : ℂ, ‖z‖ ^ (2 : ℝ≥0∞).toReal = ‖z‖ * ‖z‖ := fun z => by
    rw [ENNReal.toReal_ofNat, Real.rpow_two, sq]
  simp only [hpow]
  have hprod : Summable fun p : ι × List ι =>
      (‖(a : ι → ℂ) p.1‖ * ‖(a : ι → ℂ) p.1‖) * (‖(ω : List ι → ℂ) p.2‖ * ‖(ω : List ι → ℂ) p.2‖) :=
    Summable.mul_of_nonneg (f := fun i => ‖(a : ι → ℂ) i‖ * ‖(a : ι → ℂ) i‖)
      (g := fun w => ‖(ω : List ι → ℂ) w‖ * ‖(ω : List ι → ℂ) w‖)
      (summable_norm_mul_norm a a) (summable_norm_mul_norm ω ω)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  refine (cons_injective.summable_iff ?_).1 ?_
  · intro w hw
    cases w with
    | nil => simp [tensorCoord]
    | cons i w => exact absurd ⟨(i, w), rfl⟩ hw
  · refine hprod.congr fun p => ?_
    simp only [Function.comp, tensorCoord, norm_mul]
    ring
/-- The creation operator `ω ↦ a ⊗ ω`, as a linear map. -/
def creationL (a : Fib ι) : Fock ι →ₗ[ℂ] Fock ι where
  toFun ω := ⟨tensorCoord a ω, memℓp_tensorCoord a ω⟩
  map_add' ω ω' := lp.ext <| funext fun w => by
    cases w with
    | nil => show (0 : ℂ) = 0 + 0; simp
    | cons i w =>
      show (a : ι → ℂ) i * ((ω : List ι → ℂ) w + (ω' : List ι → ℂ) w) =
        (a : ι → ℂ) i * (ω : List ι → ℂ) w + (a : ι → ℂ) i * (ω' : List ι → ℂ) w
      ring
  map_smul' c ω := lp.ext <| funext fun w => by
    cases w with
    | nil => show (0 : ℂ) = c * 0; simp
    | cons i w =>
      show (a : ι → ℂ) i * (c * (ω : List ι → ℂ) w) = c * ((a : ι → ℂ) i * (ω : List ι → ℂ) w)
      ring
theorem inner_creationL (a b : Fib ι) (ω ω' : Fock ι) :
    ⟪creationL a ω, creationL b ω'⟫_ℂ = ⟪a, b⟫_ℂ * ⟪ω, ω'⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum,
    tsum_mul_tsum_of_summable_norm (summable_norm_inner a b) (summable_norm_inner ω ω')]
  have hsupp : Function.support (fun w => ⟪((creationL a ω : Fock ι) : List ι → ℂ) w,
      ((creationL b ω' : Fock ι) : List ι → ℂ) w⟫_ℂ) ⊆ Set.range fun p : ι × List ι => p.1 :: p.2 := by
    intro w hw
    cases w with
    | nil => exact absurd (show ⟪(0 : ℂ), (0 : ℂ)⟫_ℂ = 0 from inner_zero_left _) hw
    | cons i w => exact ⟨(i, w), rfl⟩
  refine (cons_injective.tsum_eq hsupp).symm.trans (tsum_congr fun p => ?_)
  show ⟪(a : ι → ℂ) p.1 * (ω : List ι → ℂ) p.2, (b : ι → ℂ) p.1 * (ω' : List ι → ℂ) p.2⟫_ℂ =
    ⟪(a : ι → ℂ) p.1, (b : ι → ℂ) p.1⟫_ℂ * ⟪(ω : List ι → ℂ) p.2, (ω' : List ι → ℂ) p.2⟫_ℂ
  simp only [RCLike.inner_apply, map_mul]
  ring
theorem norm_creationL (a : Fib ι) (ω : Fock ι) : ‖creationL a ω‖ = ‖a‖ * ‖ω‖ := by
  have h := inner_creationL a a ω ω
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖creationL a ω‖ ^ 2 = (‖a‖ * ‖ω‖) ^ 2 := by
    rw [mul_pow]; exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    two_ne_zero).1 h'
/-- The creation operator `ω ↦ a ⊗ ω`. -/
def creation (a : Fib ι) : Fock ι →L[ℂ] Fock ι :=
  (creationL a).mkContinuous ‖a‖ fun ω => (norm_creationL a ω).le
theorem norm_creation_le (a : Fib ι) : ‖creation a‖ ≤ ‖a‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _
/-- The annihilation operator, the adjoint of `creation a`. -/
def annihilation (a : Fib ι) : Fock ι →L[ℂ] Fock ι :=
  ContinuousLinearMap.adjoint (creation a)
theorem norm_annihilation_le (a : Fib ι) : ‖annihilation a‖ ≤ ‖a‖ := by
  rw [annihilation, LinearIsometryEquiv.norm_map]
  exact norm_creation_le a
end
end GroupApproximation.Toeplitz
