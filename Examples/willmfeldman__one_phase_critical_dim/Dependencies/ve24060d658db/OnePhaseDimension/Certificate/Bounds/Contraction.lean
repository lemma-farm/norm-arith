/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Examples.willmfeldman__one_phase_critical_dim.Dependencies.ve24060d658db.OnePhaseDimension.Certificate.Bounds.TensorBounds
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Norm bounds for contractions of tensors on `ℝ⁵`

Elementary Cauchy–Schwarz and operator-norm estimates for the contractions that occur in the
scalar graphs of the certificate:

* `OpBound M κ`: `|M v|² ≤ κ |v|²` for all `v`; `opBound_pow` gives `κ = (4/5)^k` for `M = A^k`;
* `sq_dot_le`: `⟨P, R⟩² ≤ |P|² |R|²`;
* `sq1_vecX_le`, `sq2_matX_le`: contracting a cubic tensor with vectors;
* `sq2_biOp_le`, `sq3_triOp_le`: applying matrices with operator bounds to the slots of a two- or
  three-tensor (the Kronecker operator bound `‖M₁ ⊗ ⋯ ⊗ M_r‖ ≤ ∏ ‖M_s‖`, proved one slot at a
  time).
-/
@[expose] public noncomputable section
namespace OnePhaseDimension.Certificate
open Matrix Finset
/-- `M` has squared operator norm at most `κ`. -/
def OpBound (M : Matrix (Fin 5) (Fin 5) ℝ) (κ : ℝ) : Prop := ∀ v, sq1 (M *ᵥ v) ≤ κ * sq1 v
theorem sq2_nonneg (Q : Fin 5 → Fin 5 → ℝ) : 0 ≤ sq2 Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
/-- Cauchy–Schwarz for vectors. -/
theorem sq_dot_le (P R : Fin 5 → ℝ) : (∑ a, P a * R a) ^ 2 ≤ sq1 P * sq1 R :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _
def matX (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y : Fin 5 → ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun a b => ∑ c, X a b c * y c
theorem sq2_matX_le (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y : Fin 5 → ℝ) :
    sq2 (matX X y) ≤ sq3 X * sq1 y := by
  rw [sq2, sq3, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun b _ => sq_dot_le (X a b) y
section Slots
variable {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ}
theorem sq2_op_right_le (hM : OpBound M₁ κ₁) (Q : Fin 5 → Fin 5 → ℝ) :
    sq2 (fun a a' => ∑ b', M₁ a' b' * Q a b') ≤ κ₁ * sq2 Q := by
  rw [sq2, sq2, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => hM (Q a)
/-- Applying `M` to the first slot of a two-tensor. -/
theorem sq2_op_left_le (hM : OpBound M₁ κ₁) (Q : Fin 5 → Fin 5 → ℝ) :
    sq2 (fun a a' => ∑ b, M₁ a b * Q b a') ≤ κ₁ * sq2 Q := by
  have e₁ : sq2 (fun a a' => ∑ b, M₁ a b * Q b a') = ∑ a', sq1 (M₁ *ᵥ fun b => Q b a') := by
    rw [sq2, Finset.sum_comm]; rfl
  have e₂ : sq2 Q = ∑ a', sq1 (fun b => Q b a') := by rw [sq2, Finset.sum_comm]; rfl
  rw [e₁, e₂, Finset.mul_sum]
  exact Finset.sum_le_sum fun a' _ => hM _
/-- The Kronecker bound on two-tensors: `|(M₁ ⊗ M₂)Q|² ≤ κ₁ κ₂ |Q|²`. -/
theorem sq2_biOp_le (hM₁ : OpBound M₁ κ₁) (hM₂ : OpBound M₂ κ₂) (hκ₁ : 0 ≤ κ₁)
    (Q : Fin 5 → Fin 5 → ℝ) :
    sq2 (fun a a' => ∑ b, ∑ b', M₁ a b * M₂ a' b' * Q b b') ≤ κ₁ * κ₂ * sq2 Q := by
  set T : Fin 5 → Fin 5 → ℝ := fun b a' => ∑ b', M₂ a' b' * Q b b'
  have hT : sq2 T ≤ κ₂ * sq2 Q := sq2_op_right_le hM₂ Q
  have h := sq2_op_left_le hM₁ T
  have e : (fun a a' => ∑ b, ∑ b', M₁ a b * M₂ a' b' * Q b b') =
      fun a a' => ∑ b, M₁ a b * T b a' := by
    funext a a'
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [T, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b' _ => by ring
  rw [e]
  calc _ ≤ κ₁ * sq2 T := h
    _ ≤ κ₁ * (κ₂ * sq2 Q) := mul_le_mul_of_nonneg_left hT hκ₁
    _ = _ := by ring
end Slots
end OnePhaseDimension.Certificate
