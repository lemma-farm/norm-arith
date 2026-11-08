/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.RegularityStructures.Torus.Basic
public import Mathlib.Probability.Distributions.Gaussian.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Space-time white noise

A space-time white noise on `ℝ × T³` is a family `(W(h))` of real random variables, indexed by
square-integrable functions `h`, such that every finite subfamily is a centred Gaussian vector with
covariance `E[W(hᵢ) W(hⱼ)] = ∫ hᵢ hⱼ` (the statement, Definition 2.2).

Measurability is stated explicitly. In Mathlib, `Measure.map` of a non-measurable map is a point
mass, which counts as Gaussian, and the Bochner integral of a non-measurable function is zero.
Without the measurability clauses, a non-measurable family could satisfy the remaining conditions.

Source: the statement, Definition 2.2.
-/
@[expose] public section
open MeasureTheory
namespace RegularityStructures
variable {Ω : Type*} [MeasurableSpace Ω]
end RegularityStructures
end
