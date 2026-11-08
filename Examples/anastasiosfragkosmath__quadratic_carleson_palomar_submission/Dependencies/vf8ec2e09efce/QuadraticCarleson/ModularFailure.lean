/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleModular
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Modular-estimate failure from counterexamples

The global modular estimate is defined for measurable extended-nonnegative
operators on `L0Infinity`, retaining infinite values. An abstract `o(N)`
contradiction criterion and exact positive-homogeneity normalization yield
unit-height witnesses. For the paper's `χ_N`, the modular bound is extended
to every fixed positive factor, and the non-strict analytic lower level is
converted to a strict level at half the height. The analytic lower bound
remains an explicit hypothesis, not an assertion in this file.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal
namespace QuadraticCarleson
set_option autoImplicit false
/-- A measurable extended-nonnegative-valued operator on the paper's
space of bounded compactly supported measurable functions. -/
structure NonnegativeOperator where
  toFun : L0Infinity → ℝ → ℝ≥0∞
  measurable_toFun : ∀ f, Measurable (toFun f)
instance : CoeFun NonnegativeOperator (fun _ ↦ L0Infinity → ℝ → ℝ≥0∞) :=
  ⟨NonnegativeOperator.toFun⟩
end QuadraticCarleson
