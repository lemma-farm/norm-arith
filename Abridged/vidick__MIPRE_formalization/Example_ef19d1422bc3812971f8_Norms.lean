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

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_ef19d1422bc3812971f8_Norms ====
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
/-- Normalizing a vector `u` near a unit vector `ψ` keeps it near `ψ`:
`‖u / ‖u‖ - ψ‖ ≤ 2 ‖u - ψ‖`. -/
theorem norm_toLp_normalize_sub_le (u ψ : n → ℂ)
    (hψ : ‖(toLp 2 ψ : EuclideanSpace ℂ n)‖ = 1) (hu : u ≠ 0) :
    ‖(toLp 2 (((‖(toLp 2 u : EuclideanSpace ℂ n)‖ : ℂ)⁻¹) • u - ψ) : EuclideanSpace ℂ n)‖ ≤
      2 * ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by
  set r : ℝ := ‖(toLp 2 u : EuclideanSpace ℂ n)‖ with hr
  have hrpos : 0 < r := norm_pos_iff.mpr (by simpa using hu)
  have h1 : (toLp 2 ((r : ℂ)⁻¹ • u - ψ) : EuclideanSpace ℂ n) =
      ((r : ℂ)⁻¹ • toLp 2 u - toLp 2 u) + (toLp 2 u - toLp 2 ψ) := by
    rw [toLp_sub, toLp_smul]
    abel
  have h2 : ‖(r : ℂ)⁻¹ • (toLp 2 u : EuclideanSpace ℂ n) - toLp 2 u‖ ≤
      ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by
    have e : (r : ℂ)⁻¹ • (toLp 2 u : EuclideanSpace ℂ n) - toLp 2 u =
        (((r⁻¹ - 1 : ℝ)) : ℂ) • toLp 2 u := by
      push_cast
      rw [sub_smul, one_smul]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |r⁻¹ - 1| * r = |(r⁻¹ - 1) * r| := by rw [abs_mul, abs_of_pos hrpos]
      _ = |1 - r| := by rw [sub_mul, inv_mul_cancel₀ hrpos.ne', one_mul]
      _ = |‖(toLp 2 ψ : EuclideanSpace ℂ n)‖ - ‖(toLp 2 u : EuclideanSpace ℂ n)‖| := by
          rw [hψ]
      _ ≤ ‖(toLp 2 ψ : EuclideanSpace ℂ n) - toLp 2 u‖ := abs_norm_sub_norm_le _ _
      _ = ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by rw [norm_sub_rev, toLp_sub]
  have h3 : ‖(toLp 2 u : EuclideanSpace ℂ n) - toLp 2 ψ‖ =
      ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by rw [toLp_sub]
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  linarith
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
