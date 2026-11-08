/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open MeasureTheory
/-! # Bounded-density single-site laws -/
public section
namespace FroehlichSpencer
/-- A probability law with a measurable `ENNReal` density bounded pointwise by `δ⁻¹`.

The positive parameter `δ` makes the real bound finite and positive. -/
@[expose] def HasBoundedDensity (law : Measure ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∃ g : ℝ → ENNReal,
    Measurable g ∧
    law = volume.withDensity g ∧
    ∀ t, g t ≤ ENNReal.ofReal (δ⁻¹)
end FroehlichSpencer
end
