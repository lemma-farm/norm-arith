/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.PositiveEndpointOptimization
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Measurable magnitude levels and endpoint-weight integration

This module supplies the measure-theoretic bridge from the scalar estimates
in `PositiveEndpointOptimization` to the sums over the paper's magnitude sets
`F_k`.  Extended nonnegative integrals are used throughout, so no integrability
or finiteness hypothesis is needed.
-/
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace QuadraticCarleson
namespace PositiveLevelIntegration
open PositiveEndpointOptimization
set_option autoImplicit false
/-- The paper's magnitude set `F_k`, for an arbitrary threshold sequence. -/
def magnitudeLevelSet {α : Type*} (A : ℕ → ℝ) (f : α → ℂ) (k : ℕ) : Set α :=
  {x | InMagnitudeLevel A k ‖f x‖}
@[simp] theorem mem_magnitudeLevelSet {α : Type*} {A : ℕ → ℝ}
    {f : α → ℂ} {k : ℕ} {x : α} :
    x ∈ magnitudeLevelSet A f k ↔ InMagnitudeLevel A k ‖f x‖ :=
  Iff.rfl
end PositiveLevelIntegration
end QuadraticCarleson
