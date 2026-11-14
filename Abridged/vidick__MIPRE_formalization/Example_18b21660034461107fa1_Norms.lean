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
set_option linter.unusedVariables false in
axiom _root_.MIPRE.ValueApprox.IsSkewHermitian.re_dotProduct_mulVec.{w_u_1} : ∀ {n : Type w_u_1} {S : Matrix n n ℂ} [inst : Fintype n],
  MIPRE.ValueApprox.IsSkewHermitian S → ∀ (v : n → ℂ), (Star.star v ⬝ᵥ S.mulVec v).re = 0
variable [DecidableEq n]

end IsSkewHermitian
variable [Fintype n] [DecidableEq n]

/-! ## Phases

`cayley` reaches only the unitaries `U` with `1 + U` invertible. Multiplying `U` by a unit
scalar `z` does not change the conjugation `P ↦ U P Uᴴ`, and some unit `z` always makes
`1 + z • U` invertible: `z ↦ det (1 + z • U)` is a polynomial with constant term `1`. -/

end MIPRE.ValueApprox
end

end

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_18b21660034461107fa1_Norms ====
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
set_option linter.unusedVariables false in
/-- `‖(1 + S) x‖ ≥ ‖x‖` for skew-Hermitian `S`: the cross term of `‖x + S x‖²` vanishes. -/
theorem norm_toLp_le_norm_toLp_one_add_mulVec (hS : IsSkewHermitian S) (x : n → ℂ) 
    (h_MIPRE_ValueApprox_inner_toLp_toLp : ∀ {n : Type u_1} [inst : Fintype n] (x y : n → ℂ),
      Inner.inner ℂ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = Star.star x ⬝ᵥ y)
    :
    ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ≤
      ‖(toLp 2 ((1 + S) *ᵥ x) : EuclideanSpace ℂ n)‖ := by
  have hsq : ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 ≤
      ‖(toLp 2 ((1 + S) *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 := by
    rw [Matrix.add_mulVec, one_mulVec, toLp_add, norm_add_sq (𝕜 := ℂ), h_MIPRE_ValueApprox_inner_toLp_toLp,
      RCLike.re_to_complex, hS.re_dotProduct_mulVec, mul_zero, add_zero]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

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
