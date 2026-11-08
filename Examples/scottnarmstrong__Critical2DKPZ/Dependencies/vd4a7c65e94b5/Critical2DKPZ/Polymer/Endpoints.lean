/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Polymer.Moments
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! At a fixed walk horizon, only finitely many endpoints contribute to the polymer kernel and its smoothed averages. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Critical2DKPZ.Polymer
/-- The finite set of sites reachable in a given number of steps. -/
def endpoints (w : Site) (n : ℕ) : Finset Site :=
  Finset.univ.image (fun s : Fin n → Fin 4 => walkPosition w s n)
/-- A site is reachable exactly when some finite walk ends there. -/
theorem mem_endpoints_iff (w z : Site) (n : ℕ) :
    z ∈ endpoints w n ↔ Reachable n w z := by
  simp only [endpoints, Finset.mem_image, Finset.mem_univ, true_and, Reachable]
theorem tsum_pointToPoint_mul (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    ∑' z, pointToPoint β a n w z ω * f z =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
        f (walkPosition w s n) := by
  have hs : ∀ s : Fin n → Fin 4, Summable (fun z : Site =>
      (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
        (if walkPosition w s n = z then 1 else 0) * f z) := by
    intro s
    apply summable_of_ne_finset_zero (s := {walkPosition w s n})
    intro z hz
    have hne : walkPosition w s n ≠ z := by
      simpa only [Finset.mem_singleton, not_not, ne_eq, eq_comm] using hz
    simp only [ite_eq_right hne, mul_zero, zero_mul]
  simp only [pointToPoint_eq_sum, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun s _ => hs s)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, tsum_ite_eq']
/-- The sum of the point-to-point kernel over its endpoint is the point-to-plane partition function. -/
theorem tsum_pointToPoint (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    ∑' z, pointToPoint β a n w z ω = pointToPlane β a n w ω := by
  simpa only [mul_one, pointToPlane_eq_sum] using
    tsum_pointToPoint_mul β a n w (fun _ => 1) ω
theorem srwKernel_eq_sum (n : ℕ) (w z : Site) :
    srwKernel n (z - w) = ∑ s : Fin n → Fin 4,
      (4 : ℝ)⁻¹ ^ n * if walkPosition w s n = z then 1 else 0 := by
  unfold srwKernel
  apply Finset.sum_congr rfl
  intro s _
  rw [walkPosition_eq_start_add w s n]
  simp only [eq_sub_iff_add_eq, add_comm]
/-- The simple-walk kernel vanishes at unreachable endpoints. -/
theorem srwKernel_eq_zero_of_not_mem (n : ℕ) (w z : Site)
    (hz : z ∉ endpoints w n) : srwKernel n (z - w) = 0 := by
  rw [srwKernel_eq_sum n w z]
  apply Finset.sum_eq_zero
  intro s _
  have hne : walkPosition w s n ≠ z := by
    intro hs
    exact hz ((mem_endpoints_iff w z n).2 ⟨s, hs⟩)
  simp only [ite_eq_right hne, mul_zero]
end Critical2DKPZ.Polymer
