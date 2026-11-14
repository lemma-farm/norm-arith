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

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_0a507938e1e24c1da449_Norms ====
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
omit [DecidableEq n] in
/-- An entrywise bound on a vector gives a norm bound with a factor of the dimension. -/
theorem norm_toLp_le_card_mul_of_forall_norm_le {v : n → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i, ‖v i‖ ≤ δ) : ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ≤ Fintype.card n * δ := by
  have hsq : ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 ≤ (Fintype.card n * δ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : n, δ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = Fintype.card n * δ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card n : ℝ) ^ 2 * δ ^ 2 := by
          gcongr
          exact_mod_cast Nat.le_self_pow two_ne_zero _
      _ = (Fintype.card n * δ) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

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
