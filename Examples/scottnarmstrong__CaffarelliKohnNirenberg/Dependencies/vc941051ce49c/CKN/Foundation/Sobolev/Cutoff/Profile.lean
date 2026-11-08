-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
/-!
# A quantitative smooth transition profile

This file records the one-dimensional profile used by the ball and space-time
cutoff constructions.

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. The namespace and imports are independent.

## Main definitions

* `CKN.smoothTransitionProfile`: the canonical smooth transition from `0` to
  `1`.
* `CKN.smoothTransitionProfile.derivBound`: its explicit first-derivative
  bound.

## Main results

* `smoothTransitionProfile.abs_deriv_le_eight`: the first derivative is
  bounded by `8`.
-/
noncomputable section
open Polynomial
namespace CKN
/-- The canonical smooth transition from `0` to `1`. -/
def smoothTransitionProfile : ℝ → ℝ :=
  Real.smoothTransition
namespace smoothTransitionProfile
/-- The canonical transition profile is smooth to every order. -/
theorem smooth : ContDiff ℝ (⊤ : ℕ∞) smoothTransitionProfile :=
  Real.smoothTransition.contDiff
/-- The canonical transition profile is nonnegative. -/
theorem nonneg (t : ℝ) :
    0 ≤ smoothTransitionProfile t :=
  Real.smoothTransition.nonneg t
/-- The canonical transition profile is at most `1`. -/
theorem le_one (t : ℝ) :
    smoothTransitionProfile t ≤ 1 :=
  Real.smoothTransition.le_one t
end smoothTransitionProfile
end CKN
