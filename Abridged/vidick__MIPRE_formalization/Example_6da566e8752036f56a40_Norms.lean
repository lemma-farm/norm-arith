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

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_6da566e8752036f56a40_Norms ====
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
set_option linter.unusedVariables false in
/-- An entrywise bound gives an operator-norm bound with a factor of the dimension. -/
theorem l2_opNorm_le_card_mul_of_entry_le {E : Matrix n n ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖E i j‖ ≤ δ) 
    (h_MIPRE_ValueApprox_l2_opNorm_le_of_forall : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {A : Matrix n n ℂ} {c : ℝ},
      0 ≤ c → (∀ (x : n → ℂ), ‖WithLp.toLp 2 (A.mulVec x)‖ ≤ c * ‖WithLp.toLp 2 x‖) → ‖A‖ ≤ c)
    : ‖E‖ ≤ Fintype.card n * δ := by
  refine h_MIPRE_ValueApprox_l2_opNorm_le_of_forall (by positivity) fun x => ?_
  have hrow : ∀ i, ‖(E *ᵥ x) i‖ ≤ δ * ∑ j, ‖x j‖ := fun i => by
    simp only [mulVec, dotProduct]
    calc ‖∑ j, E i j * x j‖ ≤ ∑ j, ‖E i j * x j‖ := norm_sum_le _ _
      _ = ∑ j, ‖E i j‖ * ‖x j‖ := by simp
      _ ≤ ∑ j, δ * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
      _ = δ * ∑ j, ‖x j‖ := by rw [Finset.mul_sum]
  have hcs : (∑ j, ‖x j‖) ^ 2 ≤ Fintype.card n * ∑ j, ‖x j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖x j‖)
  have hsq : ‖(toLp 2 (E *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ≤
      (Fintype.card n * δ * ‖(toLp 2 x : EuclideanSpace ℂ n)‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(E *ᵥ x) i‖ ^ 2 ≤ ∑ i, (δ * ∑ j, ‖x j‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
      _ = Fintype.card n * (δ ^ 2 * (∑ j, ‖x j‖) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow]
      _ ≤ Fintype.card n * (δ ^ 2 * (Fintype.card n * ∑ j, ‖x j‖ ^ 2)) := by gcongr
      _ = (Fintype.card n * δ) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
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
