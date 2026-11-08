-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic
public import Mathlib.Topology.Order.Monotone
set_option autoImplicit false
@[expose] public section
/-!
# Scalar threshold calculus for spherical spin mixtures

This file proves the scalar calculus used in equations `eq:pre-Phi-derivative`
and `eq:intro-plateau`, and the elementary threshold ordering in
`rem:pre-thresholds`. The covariance is represented by an actual real function.
The regularity and positivity hypotheses are explicit: this file does not assert
that a stochastic model, Parisi minimizer, or Langevin process has been constructed.
-/
namespace SlowEquilibration.Thresholds
open Set
/-- The dynamical scalar function from `def:pre-thresholds`. -/
noncomputable def A (ξ : ℝ → ℝ) (r : ℝ) : ℝ := (1 - r) * deriv ξ r / r
end SlowEquilibration.Thresholds
