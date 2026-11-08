/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Examples.willmfeldman__one_phase_critical_dim.Dependencies.ved80ba4ba870.OnePhaseDimension.Certificate.Bounds.TensorBounds
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
theorem sq3_eq_sum_sq2 (T : Fin 5 → Fin 5 → Fin 5 → ℝ) : sq3 T = ∑ a, sq2 (T a) := rfl
theorem sq3_op_last_le (hM : OpBound M₁ κ₁) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a b c => ∑ c', M₁ c c' * T a b c') ≤ κ₁ * sq3 T := by
  rw [sq3_eq_sum_sq2, sq3_eq_sum_sq2, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => sq2_op_right_le hM (T a)
/-- Applying `M` to the middle slot of a three-tensor. -/
theorem sq3_op_mid_le (hM : OpBound M₁ κ₁) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a b c => ∑ b', M₁ b b' * T a b' c) ≤ κ₁ * sq3 T := by
  rw [sq3_eq_sum_sq2, sq3_eq_sum_sq2, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => sq2_op_left_le hM (T a)
/-- Applying `M` to the first slot of a three-tensor. -/
theorem sq3_op_first_le (hM : OpBound M₁ κ₁) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a b c => ∑ a', M₁ a a' * T a' b c) ≤ κ₁ * sq3 T := by
  have e : ∀ S : Fin 5 → Fin 5 → Fin 5 → ℝ, sq3 S = ∑ b, ∑ c, sq1 (fun a => S a b c) := by
    intro S
    rw [sq3, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
  rw [e, e T, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => hM fun a => T a b c
/-- The Kronecker bound on three-tensors: `|(M₁ ⊗ M₂ ⊗ M₃)T|² ≤ κ₁ κ₂ κ₃ |T|²`. -/
theorem sq3_triOp_le (hM₁ : OpBound M₁ κ₁) (hM₂ : OpBound M₂ κ₂) (hM₃ : OpBound M₃ κ₃)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a a' a'' => ∑ b, M₁ a b * ∑ b', M₂ a' b' * ∑ b'', M₃ a'' b'' * T b b' b'') ≤
      κ₁ * κ₂ * κ₃ * sq3 T := by
  set T₃ : Fin 5 → Fin 5 → Fin 5 → ℝ := fun a b c => ∑ c', M₃ c c' * T a b c'
  set T₂ : Fin 5 → Fin 5 → Fin 5 → ℝ := fun a b c => ∑ b', M₂ b b' * T₃ a b' c
  have h₃ : sq3 T₃ ≤ κ₃ * sq3 T := sq3_op_last_le hM₃ T
  have h₂ : sq3 T₂ ≤ κ₂ * sq3 T₃ := sq3_op_mid_le hM₂ T₃
  have h₁ := sq3_op_first_le hM₁ T₂
  have e : (fun a a' a'' => ∑ b, M₁ a b * ∑ b', M₂ a' b' * ∑ b'', M₃ a'' b'' * T b b' b'') =
      fun a a' a'' => ∑ b, M₁ a b * T₂ b a' a'' := rfl
  rw [e]
  calc _ ≤ κ₁ * sq3 T₂ := h₁
    _ ≤ κ₁ * (κ₂ * (κ₃ * sq3 T)) :=
        mul_le_mul_of_nonneg_left (h₂.trans (mul_le_mul_of_nonneg_left h₃ hκ₂)) hκ₁
    _ = _ := by ring
end Slots
end OnePhaseDimension.Certificate
