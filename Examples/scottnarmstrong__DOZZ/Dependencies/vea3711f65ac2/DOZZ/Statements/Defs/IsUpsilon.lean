/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.vea3711f65ac2.DOZZ.Statements.Defs.UpsilonLog
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.IsUpsilon`. -/
@[expose] public section
open Complex MeasureTheory Set Filter Topology
namespace DOZZ
/-- `U` is the function `Υ_{γ/2}` of [KRV, (def:upsilon)]: entire, and equal to
`exp (upsilonLog γ z)` on the strip `0 < Re z < Q`. (Uniqueness is the identity theorem;
existence is part of `dozz_existence`.) -/
def IsUpsilon (γ : ℝ) (U : ℂ → ℂ) : Prop :=
  Differentiable ℂ U ∧
    ∀ z : ℂ, 0 < z.re → z.re < Q γ → U z = Complex.exp (upsilonLog γ z)
end DOZZ
