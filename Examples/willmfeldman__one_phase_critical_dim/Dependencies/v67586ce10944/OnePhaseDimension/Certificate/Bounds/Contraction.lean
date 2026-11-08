/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module
public import Examples.willmfeldman__one_phase_critical_dim.Dependencies.v67586ce10944.OnePhaseDimension.Certificate.Bounds.TensorBounds
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
theorem sq_dot_le (P R : Fin 5 → ℝ) : (∑ a, P a * R a) ^ 2 ≤ sq1 P * sq1 R :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _
/-- The vector `(X:(y ⊗ z))_a = ∑_{b,c} X_{abc} y_b z_c`. -/
def vecX (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun a => ∑ b, ∑ c, X a b c * y b * z c
theorem sum_sq_mul_sq (y z : Fin 5 → ℝ) : ∑ b, ∑ c, (y b * z c) ^ 2 = sq1 y * sq1 z := by
  simp only [sq1, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
theorem sq1_vecX_le (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y z : Fin 5 → ℝ) :
    sq1 (vecX X y z) ≤ sq3 X * sq1 y * sq1 z := by
  rw [sq1, sq3, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := sum2_mul_sq_le (X a) fun b c => y b * z c
  rw [sum_sq_mul_sq] at h
  calc vecX X y z a ^ 2 = (∑ b, ∑ c, X a b c * (y b * z c)) ^ 2 := by
        simp only [vecX, mul_assoc]
    _ ≤ _ := h
    _ = _ := by ring
section Slots
variable {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ}
end Slots
end OnePhaseDimension.Certificate
