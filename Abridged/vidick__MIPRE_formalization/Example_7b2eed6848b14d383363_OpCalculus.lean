module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.StarOrder

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_7b2eed6848b14d383363_OpCalculus ====
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
# The state calculus on a Hilbert space

The estimates of the rigidity arguments are chains of bounds `‖T ψ‖ ≤ …` for operators `T` in
front of a fixed state `ψ`. This file is that calculus for bounded operators on any complex
inner product space:

* `Op.snorm ψ T = ‖T ψ‖`, with the triangle inequality, scalars, a bound in front and an
  isometry in front;
* `Op.Bnd T K`, the bound `‖T v‖ ≤ K ‖v‖` for every `v`, closed under sums, products and
  scalars;
* `Op.qform ψ T = Re ⟨ψ, T ψ⟩`, additive in `T`, with `‖T ψ‖² = qform ψ (T* T)`.

It is the first piece of the operator calculus of Phase 1(b) of `planning/mipco-track.md`,
which restates the matrix calculus over `H →L[ℂ] H` so that the stage analyses can be read in
any model with two commuting families of measurements. The matrix calculus of
`MIPRE/Foundations/OpBound.lean` is its instance on `EuclideanSpace ℂ N` through
`Matrix.toEuclideanCLM`, and its lemmas are proved from these.

As in the matrix calculus, the bound is a relation rather than the operator norm, and nothing
here uses the Loewner order on operators: the estimates need neither.
-/
namespace MIPRE
namespace Op
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
/-! ## The bound -/
/-- `‖T v‖ ≤ K ‖v‖` for every `v`: the operator norm of `T` is at most `K`, as a relation. -/
def Bnd (T : H →L[ℂ] H) (K : ℝ) : Prop := ∀ v, ‖T v‖ ≤ K * ‖v‖
section SNorm
variable (ψ : H)
/-- `‖T ψ‖`, for a fixed state `ψ`. -/
def snorm (T : H →L[ℂ] H) : ℝ := ‖T ψ‖

end SNorm
/-! ## The quadratic form -/
section QForm
variable (ψ : H)
end QForm
/-! ## Isometries and adjoints -/
section Adjoint
variable [CompleteSpace H] (ψ : H)


set_option linter.unusedVariables false in
/-- **Replacing an operator by an isometry it is close to, in front of anything.** If `W` and
the isometry `WD` agree on the state to within `δ`, and `WD` commutes with `Z`, then `Z W` is
within `K δ` of `Z`, where `K` bounds `Z`. -/
theorem snorm_mul_swap {W WD Z : H →L[ℂ] H} {δ K : ℝ} (hWD : star WD * WD = 1)
    (hcomm : WD * Z = Z * WD) (hZ : Bnd Z K) (hK : 0 ≤ K) (hd : snorm ψ (W - WD) ≤ δ) 
    (h_MIPRE_Op_snorm_add_le : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] (ψ : H)
      (T T' : H →L[ℂ] H), MIPRE.Op.snorm ψ (T + T') ≤ MIPRE.Op.snorm ψ T + MIPRE.Op.snorm ψ T')
    (h_MIPRE_Op_snorm_mul_le : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] (ψ : H)
      {T : H →L[ℂ] H} {K : ℝ},
      MIPRE.Op.Bnd T K → ∀ (T' : H →L[ℂ] H), MIPRE.Op.snorm ψ (T * T') ≤ K * MIPRE.Op.snorm ψ T')
    (h_MIPRE_Op_snorm_mul_of_isometry : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H]
      [inst_2 : CompleteSpace H] (ψ : H) {T : H →L[ℂ] H},
      Star.star T * T = 1 → ∀ (T' : H →L[ℂ] H), MIPRE.Op.snorm ψ (T * T') = MIPRE.Op.snorm ψ T')
    :
    snorm ψ (Z * W) ≤ snorm ψ Z + K * δ := by
  have hsplit : Z * W = Z * (W - WD) + WD * Z := by
    rw [hcomm]
    noncomm_ring
  calc snorm ψ (Z * W) ≤ snorm ψ (Z * (W - WD)) + snorm ψ (WD * Z) := by
        rw [hsplit]; exact h_MIPRE_Op_snorm_add_le ψ _ _
    _ ≤ K * δ + snorm ψ Z := by
        refine add_le_add ?_ (le_of_eq (h_MIPRE_Op_snorm_mul_of_isometry ψ hWD Z))
        exact le_trans (h_MIPRE_Op_snorm_mul_le ψ hZ _) (mul_le_mul_of_nonneg_left hd hK)
    _ = snorm ψ Z + K * δ := by ring
end Adjoint
end Op
end MIPRE
end
