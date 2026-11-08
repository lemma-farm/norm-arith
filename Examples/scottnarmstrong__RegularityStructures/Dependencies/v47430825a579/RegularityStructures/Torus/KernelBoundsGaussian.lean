/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Torus.HeatKernelRegularity
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Torus.KernelBoundsBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Gaussian majorants for the torus heat kernel

The one-dimensional majorant from `HeatKernelRegularity` can be fixed at the scale `t = 1`. This
gives a summable, `t`-independent lattice majorant for `0 < t ≤ 1`, and hence the first
time-singular estimate needed for the torus kernel bounds.  The constants in this file are
introduced before any point variable; this is the convention used by Hairer's kernel estimates.

Source: [Hai14, Assumption 5.1 and (5.4)].
-/
@[expose] public noncomputable section
open Real Set
namespace RegularityStructures
theorem sq_centered_add_int_ge {y : ℝ} (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
    (n : ℤ) : y ^ 2 ≤ (y + (n : ℝ)) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · have hnle : (n : ℝ) ≤ -1 := by
      have h : (1 : ℝ) ≤ ((-n : ℤ) : ℝ) :=
        Int.cast_one_le_of_pos (show (0 : ℤ) < -n by omega)
      norm_num at h
      linarith
    have hright : 0 ≤ -(y + (n : ℝ)) := by linarith [hy.2]
    have habs : |y| ≤ -(y + (n : ℝ)) := by
      rw [abs_le]
      constructor <;> nlinarith [hy.1, hy.2]
    have hsq := (sq_le_sq₀ (abs_nonneg y) hright).2 habs
    calc
      y ^ 2 = |y| ^ 2 := (sq_abs y).symm
      _ ≤ (-(y + (n : ℝ))) ^ 2 := hsq
      _ = (y + (n : ℝ)) ^ 2 := by rw [neg_sq]
  · have hnle : (1 : ℝ) ≤ (n : ℝ) := Int.cast_one_le_of_pos hnpos
    have hright : 0 ≤ y + (n : ℝ) := by linarith [hy.1]
    have habs : |y| ≤ y + (n : ℝ) := by
      rw [abs_le]
      constructor <;> nlinarith [hy.1, hy.2]
    have hsq := (sq_le_sq₀ (abs_nonneg y) hright).2 habs
    simpa only [sq_abs] using hsq
theorem torusRep_eq_centered_add_int (x : Torus3) :
    ∃ m : Fin 3 → ℤ, torusRep x = torusCenteredRep x + fun i => (m i : ℝ) := by
  let m : Fin 3 → ℤ := fun i => if (1 / 2 : ℝ) ≤ torusRep x i then 1 else 0
  refine ⟨m, ?_⟩
  funext i
  dsimp [m, torusCenteredRep]
  split_ifs <;> ring
end RegularityStructures
end
