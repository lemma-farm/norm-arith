-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Sobolev.Ambient.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option warningAsError true
/-!
# Euclidean functions on the native ambient carrier

`Space` is a reducible abbreviation of the existing `CKN.Vec 3` carrier, so
all native-space statements use the same type as the Sobolev interfaces. The
body of `spaceEuclideanNorm` is kept definitionally identical to the
finite-sum expression used by the parabolic spatial norm.
-/
namespace CKN
/-- The native three-dimensional carrier, definitionally equal to `Vec 3`. -/
abbrev Space := Vec 3
/-- The Euclidean length given by the finite sum of coordinate squares. -/
noncomputable def spaceEuclideanNorm (x : Space) : ℝ := Real.sqrt (∑ k, x k ^ 2)
theorem space_norm_le_euclideanNorm (x : Space) :
    ‖x‖ ≤ spaceEuclideanNorm x := by
  change ‖x‖ ≤ Real.sqrt (∑ k, x k ^ 2)
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro k
  have hk : (x k) ^ 2 ≤ ∑ j, (x j) ^ 2 := by
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j => (x j) ^ 2)
      (fun j hj => sq_nonneg (x j)) (Finset.mem_univ k)
  have hsum : 0 ≤ ∑ j, (x j) ^ 2 :=
    Finset.sum_nonneg fun j hj => sq_nonneg (x j)
  have hsq := Real.sq_sqrt hsum
  have hsqrt := Real.sqrt_nonneg (∑ j, (x j) ^ 2)
  have habs : |x k| ≤ Real.sqrt (∑ j, (x j) ^ 2) := by
    exact abs_le_of_sq_le_sq (by simpa only [hsq] using hk) hsqrt
  simpa only [Real.norm_eq_abs] using
    habs
end CKN
