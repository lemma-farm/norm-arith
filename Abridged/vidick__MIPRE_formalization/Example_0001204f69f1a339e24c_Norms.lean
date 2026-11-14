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

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_0001204f69f1a339e24c_Norms ====
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


set_option linter.unusedVariables false in
/-- `|⟨x, T y⟩| ≤ ‖T‖ ‖x‖ ‖y‖`. -/
theorem norm_dotProduct_mulVec_le (T : Matrix n n ℂ) (x y : n → ℂ) 
    (h_MIPRE_ValueApprox_norm_toLp_mulVec_le : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] (A : Matrix n n ℂ) (x : n → ℂ),
      ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖)
    (h_MIPRE_ValueApprox_inner_toLp_toLp : ∀ {n : Type u_1} [inst : Fintype n] (x y : n → ℂ),
      Inner.inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = Star.star x ⬝ᵥ y)
    :
    ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤
      ‖T‖ * ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * ‖(toLp 2 y : EuclideanSpace ℂ n)‖ := by
  rw [← h_MIPRE_ValueApprox_inner_toLp_toLp]
  calc ‖⟪(toLp 2 x : EuclideanSpace ℂ n), (toLp 2 (T *ᵥ y) : EuclideanSpace ℂ n)⟫_ℂ‖
      ≤ ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * ‖(toLp 2 (T *ᵥ y) : EuclideanSpace ℂ n)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * (‖T‖ * ‖(toLp 2 y : EuclideanSpace ℂ n)‖) := by
        gcongr
        exact h_MIPRE_ValueApprox_norm_toLp_mulVec_le T y
    _ = _ := by ring

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

namespace IsPVM
variable {A : Type*} [Fintype A] {M : A → Matrix n n ℂ}

end IsPVM
end MIPRE.ValueApprox
end
