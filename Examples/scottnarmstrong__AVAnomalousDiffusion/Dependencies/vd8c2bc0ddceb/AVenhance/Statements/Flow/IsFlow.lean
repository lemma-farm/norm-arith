-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8c2bc0ddceb.Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `IsFlow` (Flow).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open Homogenization
namespace AVenhance
/-- Flow of a time-dependent field `b` on `ℝ²`: `X t x s` solves
`∂ₜ X(t,x,s) = b(t, X(t,x,s))` for all `t ∈ ℝ`, with `X(s,x,s) = x`
(source: `e.flow.m.def`, `enhance.tex` 1397-1410). -/
def IsFlow (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) : Prop :=
  (∀ x s, X s x s = x) ∧
  (∀ x s t, HasDerivAt (fun r => X r x s) (b t (X t x s)) t)
end AVenhance
