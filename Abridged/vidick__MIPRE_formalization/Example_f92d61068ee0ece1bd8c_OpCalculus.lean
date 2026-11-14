module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.StarOrder

-- ==== Examples.vidick__MIPRE_formalization.Examples.Example_f92d61068ee0ece1bd8c_OpCalculus ====
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
section SNorm
variable (ψ : H)
end SNorm
/-! ## The quadratic form -/
section QForm
variable (ψ : H)
/-- `Re ⟨ψ, T ψ⟩`. -/
def qform (T : H →L[ℂ] H) : ℝ := (⟪ψ, T ψ⟫_ℂ).re


set_option linter.unusedVariables false in
/-- **The quadratic form is monotone.** -/
theorem qform_mono [CompleteSpace H] {T T' : H →L[ℂ] H} (h : T ≤ T') 
    (h_MIPRE_Op_qform_sub : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] (ψ : H)
      (T T' : H →L[ℂ] H), MIPRE.Op.qform ψ (T - T') = MIPRE.Op.qform ψ T - MIPRE.Op.qform ψ T')
    (h_MIPRE_Op_qform_nonneg_of_nonneg : ∀ {H : Type u_1} [inst : NormedAddCommGroup H] [inst_1 : InnerProductSpace ℂ H] (ψ : H)
      [CompleteSpace H] {T : H →L[ℂ] H}, 0 ≤ T → 0 ≤ MIPRE.Op.qform ψ T)
    :
    qform ψ T ≤ qform ψ T' := by
  have h0 := h_MIPRE_Op_qform_nonneg_of_nonneg ψ (sub_nonneg.2 h)
  rw [h_MIPRE_Op_qform_sub] at h0
  linarith
end QForm
/-! ## Isometries and adjoints -/
section Adjoint
variable [CompleteSpace H] (ψ : H)
end Adjoint
end Op
end MIPRE
end
