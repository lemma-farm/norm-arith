/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# Exact signed corrections for the edge modes of a complete typed host

These formulas handle the residual after class totals and vertex-to-class
degrees have been corrected.  In the tripartite case the zero row and column
sums make both unwanted edge loads vanish.  When the completion repeats one
class, the denominator is `card A - 2`, rather than `card A - 1`: the second
copy of the repeated class contributes the missing negative row term.

The statements concern real signed weights.  They are not a positivity or a
post-deletion regularity theorem, and do not assert `KeevashPaddedSpec`.
-/
namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open Finset
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
theorem uniform_bound (x ε d : ℝ) (hx : |x| ≤ ε) (hd : 0 < d) :
    |x / d| ≤ ε / d := by
  rw [abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hx hd.le
/-- The repeated-class mode costs a factor of at most two in its numerator. -/
theorem repeated_bound (x y ε d : ℝ)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hd : 0 < d) :
    |(x + y) / d| ≤ 2 * ε / d := by
  apply uniform_bound (x + y) (2 * ε) d ?_ hd
  exact (abs_add_le x y).trans (by linarith)
end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
