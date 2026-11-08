/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
open MeasureTheory
/-! # Centered Gaussian single-site law -/
public section
namespace FroehlichSpencer
/-- The centered Gaussian law with positive variance `γ`. -/
@[expose] noncomputable def gaussianLaw (γ : ℝ) (hγ : 0 < γ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 ⟨γ, le_of_lt hγ⟩
end FroehlichSpencer
end
