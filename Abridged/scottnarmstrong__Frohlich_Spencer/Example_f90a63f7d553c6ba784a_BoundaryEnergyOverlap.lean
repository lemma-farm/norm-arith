module

public import Mathlib.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic.Common
public import Mathlib.Algebra.Order.Ring.Abs

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_f90a63f7d553c6ba784a_BoundaryEnergyOverlap ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Euclidean overlap bounds for multiscale boundary profiles

This module proves the geometric packing step behind the cross-scale energy
estimate: if a fine square neighborhood met two neighborhoods of separated
coarse squares, then the coarse squares would be too close.
-/
@[expose] public section
noncomputable section
namespace FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT

variable {L : ℕ}
/-- The Euclidean norm on two coordinate differences satisfies the triangle
inequality. -/
private theorem sqrt_sum_sq_triangle (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  let X := Real.sqrt (a ^ 2 + b ^ 2)
  let Y := Real.sqrt (c ^ 2 + d ^ 2)
  have hX : X ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [X]
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  have hY : Y ^ 2 = c ^ 2 + d ^ 2 := by
    dsimp [Y]
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg c) (sq_nonneg d))]
  have hXY : 0 ≤ X * Y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hdotSq : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * d - b * c)]
  have hdot : a * c + b * d ≤ X * Y := by
    have habs : |a * c + b * d| ≤ X * Y := by
      calc
        |a * c + b * d| = Real.sqrt ((a * c + b * d) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((X * Y) ^ 2) := Real.sqrt_le_sqrt (by
          have hprod : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (X * Y) ^ 2 := by
            rw [← hX, ← hY]
            ring
          rw [← hprod]
          exact hdotSq)
        _ = X * Y := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hXY]
    exact (le_abs_self _).trans habs
  have hsquares :
      (a + c) ^ 2 + (b + d) ^ 2 ≤ (X + Y) ^ 2 := by
    nlinarith [hX, hY, hdot]
  calc
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤ Real.sqrt ((X + Y) ^ 2) :=
      Real.sqrt_le_sqrt hsquares
    _ = X + Y := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    _ = Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := rfl
end FroehlichSpencer.BKT.Generic.PinnedCharges
end
