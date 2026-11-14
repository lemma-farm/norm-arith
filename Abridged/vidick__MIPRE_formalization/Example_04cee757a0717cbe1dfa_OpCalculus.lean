module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.StarOrder

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_04cee757a0717cbe1dfa_OpCalculus ====
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
end SNorm
/-! ## The quadratic form -/
section QForm
variable (ψ : H)
end QForm
/-! ## Isometries and adjoints -/
section Adjoint
variable [CompleteSpace H] (ψ : H)
theorem bnd_one_of_star_mul_self_le {T : H →L[ℂ] H} (h : star T * T ≤ 1) : Bnd T 1 := by
  intro v
  have hpos : (1 - star T * T).IsPositive := ContinuousLinearMap.le_def.1 h
  have h1 := hpos.re_inner_nonneg_right v
  have hsq : ‖T v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    have e : (⟪v, (1 - star T * T) v⟫_ℂ) = ⟪v, v⟫_ℂ - ⟪T v, T v⟫_ℂ := by
      show ⟪v, v - (star T) (T v)⟫_ℂ = _
      rw [inner_sub_right, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    rw [e, map_sub, inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h1
    linarith
  rw [one_mul]
  nlinarith [norm_nonneg (T v), norm_nonneg v]
end Adjoint
end Op
end MIPRE
end
