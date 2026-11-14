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

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_0f93d455257e32f77d9e_Norms ====
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


set_option linter.unusedVariables false in
/-- `‖1 ⊗ Y‖ ≤ ‖Y‖`: `1 ⊗ Y` acts as `Y` on each row. -/
theorem norm_one_kronecker_le (Y : Matrix n n ℂ) 
    (h_MIPRE_ValueApprox_l2_opNorm_le_of_forall : ∀ {n : Type (max u_1 u_2)} [inst : Fintype n] [inst_1 : DecidableEq n] {A : Matrix n n ℂ} {c : ℝ},
      0 ≤ c → (∀ (x : n → ℂ), ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ c * ‖WithLp.toLp 2 x‖) → ‖A‖ ≤ c)
    (h_MIPRE_ValueApprox_norm_toLp_mulVec_le : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] (A : Matrix n n ℂ) (x : n → ℂ),
      ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖)
    (h_MIPRE_ValueApprox_one_kronecker_mulVec : ∀ {n : Type u_1} [inst : Fintype n] {m : Type u_2} [inst_1 : Fintype m] [inst_2 : DecidableEq m]
      (Y : Matrix n n ℂ) (v : m × n → ℂ) (i : m) (j : n),
      (Matrix.kroneckerMap (fun (x1 x2 : ℂ) ↦ x1 * x2) 1 Y).mulVec v (i, j) =
        Y.mulVec (fun (l : n) ↦ v (i, l)) j)
    : ‖(1 : Matrix m m ℂ) ⊗ₖ Y‖ ≤ ‖Y‖ := by
  refine h_MIPRE_ValueApprox_l2_opNorm_le_of_forall (norm_nonneg _) fun v => ?_
  have hsq : ‖(toLp 2 (((1 : Matrix m m ℂ) ⊗ₖ Y) *ᵥ v) : EuclideanSpace ℂ (m × n))‖ ^ 2 ≤
      (‖Y‖ * ‖(toLp 2 v : EuclideanSpace ℂ (m × n))‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    calc ∑ i, ∑ j, ‖(((1 : Matrix m m ℂ) ⊗ₖ Y) *ᵥ v) (i, j)‖ ^ 2
        = ∑ i, ‖(toLp 2 (Y *ᵥ fun l => v (i, l)) : EuclideanSpace ℂ n)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [EuclideanSpace.norm_sq_eq]
          exact Finset.sum_congr rfl fun j _ => by rw [h_MIPRE_ValueApprox_one_kronecker_mulVec]
      _ ≤ ∑ i, (‖Y‖ * ‖(toLp 2 fun l => v (i, l) : EuclideanSpace ℂ n)‖) ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (h_MIPRE_ValueApprox_norm_toLp_mulVec_le Y _) 2
      _ = ‖Y‖ ^ 2 * ∑ i, ∑ j, ‖v (i, j)‖ ^ 2 := by
          simp only [mul_pow, EuclideanSpace.norm_sq_eq]
          rw [← Finset.mul_sum]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end Kronecker
/-! ## Conjugation -/

/-! ## Unitaries and projections -/

namespace IsPVM
variable {A : Type*} [Fintype A] {M : A → Matrix n n ℂ}

end IsPVM
end MIPRE.ValueApprox
end
