module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

-- ==== Examples.cenozoic_works__rhone_theory.Examples.Example_fef18937f413203eae5c_Inbreeding ====
/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Exact partial-selfing recurrence -/
@[expose] public section
namespace Rhone.Dynamics.Inbreeding
noncomputable def fullSibStep (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, (1 + 2 * z.2 + z.1) / 4)

private noncomputable def sibError (z : ℝ × ℝ) : ℝ := |1 - z.1| + 2 * |1 - z.2|
private axiom sibError_step (z : ℝ × ℝ) : sibError (fullSibStep z) ≤ sibError z
private axiom sibError_two_steps (z : ℝ × ℝ) :
    sibError (fullSibStep (fullSibStep z)) ≤ (3 / 4 : ℝ) * sibError z
private theorem sibError_iterate (z : ℝ × ℝ) (t : ℕ) :
    sibError ((fullSibStep^[t]) z) ≤ (3 / 4 : ℝ) ^ (t / 2) * sibError z := by
  induction t using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using sibError_step z
  | more t ih _ =>
    have ht : (t + 2) / 2 = t / 2 + 1 := by omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ht, pow_succ]
    calc
      sibError (fullSibStep (fullSibStep ((fullSibStep^[t]) z))) ≤
          (3 / 4 : ℝ) * sibError ((fullSibStep^[t]) z) := sibError_two_steps _
      _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ (t / 2) * sibError z) := by
        exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by ring
end Rhone.Dynamics.Inbreeding
