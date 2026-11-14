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

-- ==== Examples.vidick__MIPRE_formalization.Dependencies.v080e9ee923f8.MIPRE.Foundations.ValueApprox.Cayley ====
public section
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
# The Cayley transform

`cayley S = (1 - S) * (1 + S)⁻¹` maps skew-Hermitian matrices to unitaries, and every
unitary `U` for which `1 + U` is invertible is `cayley S` for the skew-Hermitian
`S = (1 - U) * (1 + U)⁻¹`; multiplying `U` by a suitable unit scalar `z` always makes
`1 + z • U` invertible, and `(z • U) P (z • U)ᴴ = U P Uᴴ`, so up to a phase every unitary is a
Cayley transform. This is the parametrization of unitaries by which the enumeration of
`lem:value-lower-approx` reaches exact unitaries with Gaussian-rational entries: the Cayley
transform of a skew-Hermitian matrix with Gaussian-rational entries has Gaussian-rational
entries, and the transform is `2`-Lipschitz (`MIPRE.Foundations.ValueApprox.Norms`), so
rounding `S` entrywise approximates `U`.

The one analytic input is `IsSkewHermitian.mulVec_one_add_eq_zero`: for skew-Hermitian
`S`, `⟨v, S v⟩` is purely imaginary, so `(1 + S) v = 0` forces `v = 0`.
-/
namespace MIPRE.ValueApprox
open Matrix Polynomial
open scoped ComplexOrder
variable {n : Type*}
/-- Skew-Hermitian matrices: `Sᴴ = -S`. -/
def IsSkewHermitian (S : Matrix n n ℂ) : Prop := Sᴴ = -S
namespace IsSkewHermitian
variable {S : Matrix n n ℂ}

variable [Fintype n]

variable [DecidableEq n]

end IsSkewHermitian
variable [Fintype n] [DecidableEq n]
/-- The Cayley transform `(1 - S) * (1 + S)⁻¹`. -/
noncomputable def cayley (S : Matrix n n ℂ) : Matrix n n ℂ := (1 - S) * (1 + S)⁻¹

/-! ## Phases

`cayley` reaches only the unitaries `U` with `1 + U` invertible. Multiplying `U` by a unit
scalar `z` does not change the conjugation `P ↦ U P Uᴴ`, and some unit `z` always makes
`1 + z • U` invertible: `z ↦ det (1 + z • U)` is a polynomial with constant term `1`. -/

end MIPRE.ValueApprox
end

end

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_ef8cd32a253e4431cde8_Norms ====
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

/-- `‖(1 + S)⁻¹‖ ≤ 1` for skew-Hermitian `S`. -/
axiom norm_inv_one_add_le (hS : IsSkewHermitian S) : ‖(1 + S)⁻¹‖ ≤ 1
end IsSkewHermitian
/-- The resolvent identity for the Cayley transform. -/
axiom cayley_sub_cayley {S T : Matrix n n ℂ} (hS : IsSkewHermitian S) (hT : IsSkewHermitian T) :
    cayley S - cayley T = (2 : ℂ) • ((1 + S)⁻¹ * (T - S) * (1 + T)⁻¹)
/-- The Cayley transform is `2`-Lipschitz on skew-Hermitian matrices. -/
theorem norm_cayley_sub_cayley_le {S T : Matrix n n ℂ} (hS : IsSkewHermitian S)
    (hT : IsSkewHermitian T) : ‖cayley S - cayley T‖ ≤ 2 * ‖S - T‖ := by
  have h3 : ‖(1 + S)⁻¹ * (T - S) * (1 + T)⁻¹‖ ≤ ‖S - T‖ := by
    calc ‖(1 + S)⁻¹ * (T - S) * (1 + T)⁻¹‖ ≤ ‖(1 + S)⁻¹‖ * ‖T - S‖ * ‖(1 + T)⁻¹‖ :=
          norm_mul₃_le
      _ ≤ 1 * ‖T - S‖ * 1 := by
          gcongr
          · exact hS.norm_inv_one_add_le
          · exact hT.norm_inv_one_add_le
      _ = ‖S - T‖ := by rw [one_mul, mul_one, norm_sub_rev]
  rw [cayley_sub_cayley hS hT, norm_smul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith
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
