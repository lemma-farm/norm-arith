/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.Definitions
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Scalar optimization in the positive endpoint argument

This file isolates the numerical part of the high--low decomposition in the
positive endpoint proof of arXiv:2609.04101v1.  In particular it records the
two choices of magnitude thresholds and scale cutoffs made at the end of the
proof and turns membership in a magnitude level into the corresponding Orlicz
weight.

We use exponential notation for real powers of two.  Thus
`lacunaryScale k = 2^(2^k)` and
`lacunaryAmplitude k = 2^(2^(2^k))`, exactly the paper's lacunary choice.
-/
open Filter Set
open scoped Topology
namespace QuadraticCarleson
namespace PositiveEndpointOptimization
set_option autoImplicit false
/-- Membership in the `k`th magnitude band.  This is the scalar content of
the paper's set `F_k`, applied to `t = |f x|`. -/
def InMagnitudeLevel (A : ℕ → ℝ) (k : ℕ) (t : ℝ) : Prop :=
  if k = 0 then 0 ≤ t ∧ t ≤ A 0
  else A (k - 1) < t ∧ t ≤ A k
theorem InMagnitudeLevel.nonneg {A : ℕ → ℝ} {k : ℕ} {t : ℝ}
    (hA : ∀ j, 0 ≤ A j) (h : InMagnitudeLevel A k t) : 0 ≤ t := by
  by_cases hk : k = 0
  · simp only [InMagnitudeLevel, hk] at h
    exact h.1
  · simp only [InMagnitudeLevel, hk] at h
    exact (hA (k - 1)).trans h.1.le
end PositiveEndpointOptimization
end QuadraticCarleson
