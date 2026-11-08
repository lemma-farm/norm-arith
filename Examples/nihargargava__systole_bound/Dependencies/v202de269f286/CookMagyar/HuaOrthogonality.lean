module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.HuaShift
@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace SystolicGrowth
namespace CookMagyarCircle
/-! # Unweighted cubic moment orthogonality

The shift estimate is stated as an integral. This module identifies its
unweighted moments with the finite solution counts already bounded in
`HuaEstimate`. -/
/-- Write the range-indexed unweighted cubic sum as a `Fin`-indexed sum. -/
theorem cubicUnweightedExpSum_eq_finSum (α : ℝ) (N : ℕ) :
    cubicUnweightedExpSum α N =
      ∑ x : Fin (N + 1), addChar α (primeCubic x.val) := by
  unfold cubicUnweightedExpSum
  exact (Fin.sum_univ_eq_sum_range
    (fun m : ℕ => addChar α (primeCubic m)) (N + 1)).symm
end CookMagyarCircle
end SystolicGrowth
