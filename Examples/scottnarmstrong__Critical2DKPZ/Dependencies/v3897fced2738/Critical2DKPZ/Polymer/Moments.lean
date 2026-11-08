/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Polymer.Basic
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Polymer.Gaussian
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Finite-horizon polymer path weights and partition functions have finite moments of every positive order under Gaussian disorder. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Critical2DKPZ.Polymer
/-- The disorder coordinate at a strictly positive time along a prescribed walk. -/
def pathIndex (a : ℕ) (w : Site) {n : ℕ} (s : Fin n → Fin 4)
    (j : ↥(Finset.Icc 1 n)) : ℕ × Site :=
  (a + j.val, walkPosition w s j.val)
/-- Distinct times along a path yield distinct time-space disorder indices. -/
theorem pathIndex_injective (a : ℕ) (w : Site) {n : ℕ} (s : Fin n → Fin 4) :
    Function.Injective (pathIndex a w s) := by
  intro i j h
  apply Subtype.ext
  have htime := congrArg Prod.fst h
  simpa only [pathIndex, Nat.add_left_cancel_iff] using htime
/-- A path weight is a finite Gaussian exponential. -/
theorem pathWeight_eq_finiteExp (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) :
    pathWeight β a w s =
      finiteExp (pathIndex a w s) (fun _ => β)
        (-(∑ _j : ↥(Finset.Icc 1 n), β ^ 2 / 2)) := by
  funext ω
  change Real.exp (∑ j ∈ Finset.Icc 1 n,
    (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2)) =
    Real.exp ((∑ j : ↥(Finset.Icc 1 n), β * ω (a + j.val, walkPosition w s j.val)) -
      ∑ _j : ↥(Finset.Icc 1 n), β ^ 2 / 2)
  rw [← Finset.sum_sub_distrib]
  congr 1
  exact (Finset.sum_coe_sort (Finset.Icc 1 n)
    (fun j => β * ω (a + j, walkPosition w s j) - β ^ 2 / 2)).symm
/-- Each normalized polymer path weight has expectation one. -/
theorem integral_pathWeight (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) :
    ∫ ω, pathWeight β a w s ω ∂disorderLaw = 1 := by
  rw [pathWeight_eq_finiteExp,
    integral_finiteExp _ (pathIndex_injective a w s)]
  simp only [add_neg_cancel, Real.exp_zero]
/-- The polymer path weight is integrable. -/
theorem integrable_pathWeight (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) :
    Integrable (pathWeight β a w s) disorderLaw := by
  rw [pathWeight_eq_finiteExp]
  exact integrable_finiteExp _ (pathIndex_injective a w s) _ _
theorem integral_pointToPoint (β : ℝ) (a n : ℕ) (w z : Site) :
    ∫ ω, pointToPoint β a n w z ω ∂disorderLaw = srwKernel n (z - w) := by
  change (∫ ω, ∑ s : Fin n → Fin 4,
    (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
      if walkPosition w s n = z then 1 else 0 ∂disorderLaw) = _
  rw [integral_finsetSum _ fun s _ =>
    ((integrable_pathWeight β a w s).const_mul _).mul_const _]
  simp only [integral_mul_const, integral_const_mul, integral_pathWeight, mul_one, srwKernel]
  apply Finset.sum_congr rfl
  intro s _
  rw [walkPosition_eq_start_add w s n]
  simp only [eq_sub_iff_add_eq, add_comm]
end Critical2DKPZ.Polymer
