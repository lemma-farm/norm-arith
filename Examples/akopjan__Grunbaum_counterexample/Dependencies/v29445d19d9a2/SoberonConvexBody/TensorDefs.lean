import Mathlib
set_option linter.deprecated false
set_option linter.unusedVariables false
/-!
# The analytic tensors from Soberon's Theorem 2

This file defines the explicit tensors used in Section 3 of Soberon's v2
proof.  The elementary polarization identities are proved here.  The global nonvanishing statement remains in Tensors.lean. This module
contains only definitions and elementary proofs, so it can be checked separately.
-/
noncomputable section
namespace SoberonConvexBody
namespace Tensors
open scoped BigOperators
abbrev E4 := EuclideanSpace ℝ (Fin 4)
local notation "x₀(" x ")" => x (0 : Fin 4)
local notation "x₁(" x ")" => x (1 : Fin 4)
local notation "x₂(" x ")" => x (2 : Fin 4)
local notation "x₃(" x ")" => x (3 : Fin 4)
def IsONFrame (q : Fin 4 → E4) : Prop :=
  ∀ i j, inner ℝ (q i) (q j) = if i = j then 1 else 0
/-- Every vector in an orthonormal frame has norm one. -/
theorem IsONFrame.norm_eq_one {q : Fin 4 → E4} (hq : IsONFrame q) (i : Fin 4) :
    ‖q i‖ = 1 := by
  have hi : inner ℝ (q i) (q i) = 1 := by simpa using hq i i
  rw [real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (q i)]
end Tensors
end SoberonConvexBody
