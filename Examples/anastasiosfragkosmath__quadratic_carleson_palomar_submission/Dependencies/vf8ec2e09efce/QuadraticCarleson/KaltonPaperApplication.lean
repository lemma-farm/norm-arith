/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KaltonEndpoint
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Countable block suprema followed by the paper's Kalton summation

The block outputs are extended nonnegative real functions, so the genuine
supremum and sum retain infinite values. We prove the block union bound and
apply the existing countable Kalton theorem to measurable, finitely supported,
capped approximations. Their monotone limit recovers the exact countable
expression, without assuming pointwise convergence of the original series.
-/
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace QuadraticCarleson
namespace KaltonPaperApplication
open KaltonEndpoint
set_option autoImplicit false
/-- The distribution-function weak bound for an extended nonnegative output. -/
def HasExtendedWeakL1Bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ℝ) (F : X → ℝ≥0∞) : Prop :=
  0 ≤ A ∧ ∀ a : ℝ, 0 < a →
    ENNReal.ofReal a * μ {x | ENNReal.ofReal a < F x} ≤ ENNReal.ofReal A
end KaltonPaperApplication
end QuadraticCarleson
