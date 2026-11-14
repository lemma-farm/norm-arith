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

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_cdf9b7e797f61c631136_Norms ====
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

/-- `‖X ⊗ 1‖ ≤ ‖X‖`: `X ⊗ 1` acts as `X` on each column. -/
axiom norm_kronecker_one_le (X : Matrix m m ℂ) : ‖X ⊗ₖ (1 : Matrix n n ℂ)‖ ≤ ‖X‖
/-- `‖1 ⊗ Y‖ ≤ ‖Y‖`: `1 ⊗ Y` acts as `Y` on each row. -/
axiom norm_one_kronecker_le (Y : Matrix n n ℂ) : ‖(1 : Matrix m m ℂ) ⊗ₖ Y‖ ≤ ‖Y‖
/-- The L2 operator norm is submultiplicative for Kronecker products. -/
theorem norm_kronecker_le (X : Matrix m m ℂ) (Y : Matrix n n ℂ) : ‖X ⊗ₖ Y‖ ≤ ‖X‖ * ‖Y‖ := by
  have h : X ⊗ₖ Y = (X ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ Y) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h]
  calc ‖(X ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ Y)‖
      ≤ ‖X ⊗ₖ (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix m m ℂ) ⊗ₖ Y‖ := norm_mul_le _ _
    _ ≤ ‖X‖ * ‖Y‖ :=
        mul_le_mul (norm_kronecker_one_le X) (norm_one_kronecker_le Y) (norm_nonneg _)
          (norm_nonneg _)
end Kronecker
/-! ## Conjugation -/

/-! ## Unitaries and projections -/

namespace IsPVM
variable {A : Type*} [Fintype A] {M : A → Matrix n n ℂ}

end IsPVM
end MIPRE.ValueApprox
end
