module

public import Mathlib
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.Normed.Module.Basic

-- ==== Examples.AIQ_Kitware__aiq_yu_wang_samworth_2015_useful_variant_davis_kahan_statisticians_formalization.Examples.Example_a176a224293c360382c4_BoundedSharpEstimates ====
/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
set_option autoImplicit false
set_option pp.unicode.fun true
/-!
# Sharp contractive-branch majorant for bounded Riccati solutions

This leaf module solves the scalar quadratic inequality produced by the
interval/exterior Sylvester estimate.  On the contractive branch, the solution
norm is bounded by the smaller root of the Riccati majorant polynomial.

The result is stated in an algebraic square-root form.  This keeps the operator
argument independent of trigonometric normalization and exposes the exact
scalar endpoint needed by later continuation and branch-selection proofs.
-/
namespace TauCeti
namespace DavisKahanExt
open scoped InnerProductSpace
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]


set_option linter.unusedVariables false in
/-- A near norm-attaining vector and its normalized image form an approximate
singular pair.  The adjoint defect is bounded by the square-root error naturally
produced by the polarization identity. -/
theorem exists_near_singular_pair
    (X : E0 →L[ℂ] E1) {ε : ℝ}
    (hε0 : 0 < ε) (hεt : ε < ‖X‖) 
    (h_TauCeti_DavisKahanExt_exists_unit_norm_apply_gt_sub : ∀ {E0 : Type u_1} [inst : NormedAddCommGroup E0] [inst_1 : InnerProductSpace ℂ E0] {E1 : Type u_2}
      [inst_2 : NormedAddCommGroup E1] [inst_3 : InnerProductSpace ℂ E1] (X : E0 →L[ℂ] E1) {ε : ℝ},
      0 < ε → ε < ‖X‖ → ∃ (x : E0), ‖x‖ = 1 ∧ ‖(X : E0 → E1) x‖ > ‖X‖ - ε)
    (h_TauCeti_DavisKahanExt_adjoint_defect_sq_le_of_normalized_pair : ∀ {E0 : Type u_1} [inst : NormedAddCommGroup E0] [inst_1 : InnerProductSpace ℂ E0]
      [inst_2 : CompleteSpace E0] {E1 : Type u_2} [inst_3 : NormedAddCommGroup E1]
      [inst_4 : InnerProductSpace ℂ E1] [inst_5 : CompleteSpace E1] (X : E0 →L[ℂ] E1) {x : E0} {y : E1}
      {s : ℝ},
      ‖x‖ = 1 →
        ‖y‖ = 1 →
          (X : E0 → E1) x = (↑s : ℂ) • y →
            ‖((ContinuousLinearMap.adjoint : (E0 →L[ℂ] E1) → E1 →L[ℂ] E0) X : E1 → E0) y -
                    (↑‖X‖ : ℂ) • x‖ ^
                2 ≤
              2 * ‖X‖ * (‖X‖ - s))
    :
    ∃ (x : E0) (y : E1) (s : ℝ),
      ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      ‖X‖ - ε < s ∧ s ≤ ‖X‖ ∧
      X x = (s : ℂ) • y ∧
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ≤
        Real.sqrt (2 * ‖X‖ * ε) := by
  obtain ⟨x, hxnorm, hxnear⟩ := h_TauCeti_DavisKahanExt_exists_unit_norm_apply_gt_sub X hε0 hεt
  set s : ℝ := ‖X x‖ with hs
  have hspos : 0 < s := by
    have hsubpos : 0 < ‖X‖ - ε := sub_pos.mpr hεt
    exact hsubpos.trans hxnear
  set y : E1 := (((s⁻¹ : ℝ) : ℂ) • X x) with hy
  have hynorm : ‖y‖ = 1 := by
    rw [hy, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr hspos.le), ← hs,
      inv_mul_cancel₀ hspos.ne']
  have hXx : X x = (s : ℂ) • y := by
    rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hspos.ne',
      Complex.ofReal_one, one_smul]
  have hsle : s ≤ ‖X‖ := by
    have h := X.le_opNorm x
    rw [hxnorm, mul_one] at h
    simpa [hs] using h
  have hdef_sq :=
    h_TauCeti_DavisKahanExt_adjoint_defect_sq_le_of_normalized_pair X hxnorm hynorm hXx
  have hgap : ‖X‖ - s < ε := by linarith
  have hrad_le :
      2 * ‖X‖ * (‖X‖ - s) ≤ 2 * ‖X‖ * ε := by
    exact mul_le_mul_of_nonneg_left hgap.le
      (mul_nonneg (by norm_num) (norm_nonneg X))
  have hdef_sq' :
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ^ 2 ≤ 2 * ‖X‖ * ε :=
    hdef_sq.trans hrad_le
  have hrad0 : 0 ≤ 2 * ‖X‖ * ε :=
    mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg X)) hε0.le
  have hdef :
      ‖X.adjoint y - (‖X‖ : ℂ) • x‖ ≤ Real.sqrt (2 * ‖X‖ * ε) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hrad0]
    exact hdef_sq'
  exact ⟨x, y, s, hxnorm, hynorm, hxnear, hsle, hXx, hdef⟩
end DavisKahanExt
end TauCeti