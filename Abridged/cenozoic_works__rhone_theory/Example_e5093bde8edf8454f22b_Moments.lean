module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

-- ==== Examples.cenozoic_works__rhone_theory.Dependencies.v9a411977d6de.Rhone.Statistics.DependenceBudget.Transfer ====
public section
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite whole-data transfer bounds; not historical bytes -/
@[expose] public section
open scoped BigOperators
namespace Rhone.Statistics.DependenceBudget
structure Law (X : Type*) [Fintype X] where
  mass : X → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1
variable {X : Type*} [Fintype X]
noncomputable def rejection (P : Law X) (φ : X → ℝ) : ℝ :=
  ∑ x, P.mass x * φ x

end Rhone.Statistics.DependenceBudget

end
end

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_e5093bde8edf8454f22b_Moments ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # One-third calibration and log-moment bounds -/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.VarianceAwarePairBetting
open DependenceBudget 
variable {X : Type*} [Fintype X]
def tuning (δ r : ℝ) : ℝ := δ / (3 * r)
def signal (δ r : ℝ) : ℝ := δ ^ 2 / r


set_option linter.unusedVariables false in
theorem source_log_second (P : Law X) (Z : X → ℝ) {δ r : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hZ : ∀ x, |Z x| ≤ 1)
    (hs : rejection P (fun x => Z x ^ 2) = r) 
    (h_Rhone_Statistics_VarianceAwarePairBetting_tuning_product_bound : ∀ {δ r : ℝ},
      0 < δ →
        δ ≤ r → ∀ {z : ℝ}, |z| ≤ 1 → |Rhone.Statistics.VarianceAwarePairBetting.tuning δ r * z| ≤ 1 / 3)
    (h_Rhone_Statistics_VarianceAwarePairBetting_log_one_add_sq_upper : ∀ {x : ℝ}, |x| ≤ 1 / 3 → Real.log (1 + x) ^ 2 ≤ 9 / 4 * x ^ 2)
    :
    rejection P (fun x => Real.log (1 + tuning δ r * Z x) ^ 2) ≤ signal δ r / 4 := by
  have hr := hδ.trans_le hδr
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (h_Rhone_Statistics_VarianceAwarePairBetting_log_one_add_sq_upper (h_Rhone_Statistics_VarianceAwarePairBetting_tuning_product_bound hδ hδr (hZ x)))
      (P.nonneg x))
  have he : (∑ x, P.mass x * (9 / 4 * (tuning δ r * Z x) ^ 2)) =
      9 / 4 * tuning δ r ^ 2 * rejection P (fun x => Z x ^ 2) := by
    simp only [rejection, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  rw [he, hs] at h
  have ha : 9 / 4 * tuning δ r ^ 2 * r = signal δ r / 4 := by
    unfold tuning signal
    field_simp [ne_of_gt hr]
    ring
  rw [ha] at h
  exact h
end Rhone.Statistics.VarianceAwarePairBetting
