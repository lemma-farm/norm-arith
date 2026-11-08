/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.PathExpansion
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Geometric resolvent identity and the multiscale decay iteration

The geometric resolvent identity in column form: for `x ∈ B ⊆ Λ` and `y ∈ Λ \ B`,
`G_Λ(x, y) = - ∑_{k ∈ B, k' ∈ Λ \ B} G_B(x, k) a(k, k') G_Λ(k', y)`, assuming only invertibility
of the two restricted operators.

Iterating it gives the decay estimate
`‖G_Λ(x, y)‖ ≤ θ ^ ⌊d(x, y) / R⌋ * max_w ‖G_Λ(w, y)‖` used in the multiscale argument of
Fröhlich–Spencer (1983), Fröhlich–Spencer (1983).
-/
@[expose] public section
open Matrix
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}
/-- Geometric resolvent identity in column form: for `x ∈ B ⊆ Λ` and `y ∈ Λ \ B`,
`G_Λ(x, y) = -∑_{k ∈ B, k' ∈ Λ \ B} G_B(x, k) a(k, k') G_Λ(k', y)`, where
`G_Λ(x, y) = resolventColumn a v Λ z y x`. Only invertibility is assumed (any `z`, no Hermitian
hypothesis). -/
theorem resolventColumn_eq_neg_sum_coupling (v : X → ℝ) {Λ B : Finset X} (hBΛ : B ⊆ Λ) {z : ℂ}
    (hΛ : IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)))
    (hB : IsUnit (restrictedOp a v B - z • (1 : Matrix B B ℂ)))
    {x y : X} (hx : x ∈ B) (hy : y ∈ Λ) (hyB : y ∉ B) :
    resolventColumn a v Λ z y x =
      -∑ k ∈ B, ∑ k' ∈ Λ \ B, resolventColumn a v B z k x * a k k' *
        resolventColumn a v Λ z y k' := by
  set g := resolventColumn a v Λ z y with hg
  set M := restrictedOp a v B - z • (1 : Matrix B B ℂ) with hM
  let r : B → ℂ := fun u => -∑ k' ∈ Λ \ B, a u k' * g k'
  have hMg : M *ᵥ (fun w : B => g w) = r := by
    funext u
    have hrow := resolventColumn_row_of_isUnit (a := a) v Λ hΛ hy (hBΛ u.2)
    have huy : (u : X) ≠ y := fun h => hyB (h ▸ u.2)
    have h0 : (if (u : X) = y then (1 : ℂ) else 0) = 0 := by simp [huy]
    rw [h0, ← Finset.sum_sdiff hBΛ (f := fun w => a u w * g w)] at hrow
    rw [hM, restrictedOp_sub_smul_mulVec_apply]
    simp only [r]
    rw [← hg] at hrow
    linear_combination hrow
  have hgB : (fun w : B => g w) = M⁻¹ *ᵥ r := by
    rw [← hMg, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hB), Matrix.one_mulVec]
  have h1 := congrFun hgB ⟨x, hx⟩
  simp only [Matrix.mulVec, dotProduct] at h1
  change g x = _ at h1
  have e : ∀ k ∈ B, ∑ k' ∈ Λ \ B, resolventColumn a v B z k x * a k k' * g k' =
      resolventColumn a v B z k x * ∑ k' ∈ Λ \ B, a k k' * g k' := fun k _ => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k' _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl e, h1, ← Finset.sum_coe_sort B, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [resolventColumn_of_mem a v z hx k.2]
  simp only [r]
  ring
end FroehlichSpencer.Infra
