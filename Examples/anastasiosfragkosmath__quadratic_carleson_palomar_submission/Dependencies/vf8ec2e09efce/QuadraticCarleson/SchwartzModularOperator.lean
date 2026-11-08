/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleSchwartz
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.ModularFailure
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The measurable lacunary operator and its Schwartz modular estimate

The canonical quadratic principal values are measurable as pointwise
limits of measurable symmetric truncations. Their countable dyadic
supremum is therefore a measurable extended-nonnegative-valued operator.
The modular estimate is tested on compactly supported Schwartz functions,
the literal intersection of Schwartz space with the paper's `L0Infinity`
test domain. No operator on arbitrary `L0Infinity` is defined here.
-/
open MeasureTheory Filter Set Asymptotics
open scoped SchwartzMap Topology ENNReal
namespace QuadraticCarleson
set_option autoImplicit false
structure SchwartzNonnegativeOperator where
  toFun : 𝓢(ℝ, ℂ) → ℝ → ℝ≥0∞
  measurable_toFun : ∀ f, Measurable (toFun f)
instance : CoeFun SchwartzNonnegativeOperator (fun _ ↦ 𝓢(ℝ, ℂ) → ℝ → ℝ≥0∞) :=
  ⟨SchwartzNonnegativeOperator.toFun⟩
end QuadraticCarleson
