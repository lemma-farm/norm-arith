/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.Defs.UpsilonLogIntegrand
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.upsilonLog`. -/
@[expose] public section
open Complex MeasureTheory Set Filter Topology
namespace DOZZ
/-- `ln Υ_{γ/2}(z) = ∫₀^∞ …` ([KRV, (def:upsilon)]), meaningful on the strip `0 < Re z < Q`. -/
noncomputable def upsilonLog (γ : ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), upsilonLogIntegrand γ z t
end DOZZ
