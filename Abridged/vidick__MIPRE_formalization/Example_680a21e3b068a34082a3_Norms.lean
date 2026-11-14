module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Peel
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.Chebyshev

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_680a21e3b068a34082a3_Norms ====
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
set_option autoImplicit false
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
@[expose] public section
/-!
# Operator-norm estimates for the enumeration of strategies

The analytic input of `lem:value-lower-approx`, in the L2 operator norm on matrices
(`Matrix.Norms.L2Operator`), with vectors `x : n → ℂ` measured in `ℂ^n` as `toLp 2 x`:

* `IsSkewHermitian.norm_inv_one_add_le`: `‖(1 + S)⁻¹‖ ≤ 1` for skew-Hermitian `S`;
* `norm_cayley_sub_cayley_le`: the Cayley transform is `2`-Lipschitz on skew-Hermitian
  matrices;
* `l2_opNorm_le_card_mul_of_entry_le`: an entrywise bound `δ` gives `‖E‖ ≤ n δ`, which is what
  rounding a matrix entrywise costs;
* unitaries and projections have norm at most `1` (`norm_le_one_of_mem_unitaryGroup`,
  `norm_le_one_of_isProj`).
-/
namespace MIPRE.ValueApprox
open Matrix WithLp
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace
variable {n : Type*} [Fintype n] [DecidableEq n]
/-! ## Vectors of `ℂ^n` -/

/-! ## Skew-Hermitian matrices and the Cayley transform -/
namespace IsSkewHermitian
variable {S T : Matrix n n ℂ}

end IsSkewHermitian

/-! ## Entrywise bounds -/

/-! ## Vectors with small entries -/

/-! ## Kronecker products -/
section Kronecker
open scoped Kronecker
variable {m : Type*} [Fintype m] [DecidableEq m]

end Kronecker
/-! ## Conjugation -/

/-! ## Unitaries and projections -/


set_option linter.unusedVariables false in
/-- A self-adjoint idempotent has norm at most `1`. -/
theorem norm_le_one_of_isProj {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) 
    (h_MIPRE_ValueApprox_dotProduct_conjTranspose_mul_self : ∀ {n : Type u_1} [inst : Fintype n] (N : Matrix n n ℂ) (v : n → ℂ),
      Star.star v ⬝ᵥ (N.conjTranspose * N).mulVec v = Star.star (N.mulVec v) ⬝ᵥ N.mulVec v)
    (h_MIPRE_ValueApprox_l2_opNorm_le_of_forall : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {A : Matrix n n ℂ} {c : ℝ},
      0 ≤ c → (∀ (x : n → ℂ), ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ c * ‖WithLp.toLp 2 x‖) → ‖A‖ ≤ c)
    (h_MIPRE_ValueApprox_inner_toLp_toLp : ∀ {n : Type u_1} [inst : Fintype n] (x y : n → ℂ),
      Inner.inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = Star.star x ⬝ᵥ y)
    (h_MIPRE_ValueApprox_norm_sq_toLp : ∀ {n : Type u_1} [inst : Fintype n] (x : n → ℂ), ‖WithLp.toLp 2 x‖ ^ 2 = (Star.star x ⬝ᵥ x).re)
    : ‖P‖ ≤ 1 := by
  refine h_MIPRE_ValueApprox_l2_opNorm_le_of_forall zero_le_one fun x => ?_
  rw [one_mul]
  have hsq : ‖(toLp 2 (P *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ≤
      ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * ‖(toLp 2 (P *ᵥ x) : EuclideanSpace ℂ n)‖ := by
    rw [h_MIPRE_ValueApprox_norm_sq_toLp, ← h_MIPRE_ValueApprox_dotProduct_conjTranspose_mul_self, hP, hPP, ← h_MIPRE_ValueApprox_inner_toLp_toLp]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  rcases (norm_nonneg (toLp 2 (P *ᵥ x) : EuclideanSpace ℂ n)).lt_or_eq with hpos | hzero
  · rw [sq] at hsq
    exact le_of_mul_le_mul_right hsq hpos
  · rw [← hzero]
    exact norm_nonneg _
namespace IsPVM
variable {A : Type*} [Fintype A] {M : A → Matrix n n ℂ}

end IsPVM
end MIPRE.ValueApprox
end
