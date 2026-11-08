/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.GMC.IsCenteredGaussianField
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.fieldChaosMass`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- Finite-cutoff continuum Wick chaos mass. -/
noncomputable def fieldChaosMass {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (ν : Measure S) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, (h x : ℝ≥0∞) *
    ENNReal.ofReal (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P)) ∂ν
end DOZZ
