/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.Basic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Combes–Thomas bound in finite volume

For a Hermitian kernel `a` of range one (with respect to a pseudo-distance `d`) and row bound `K`,
every entry of the finite-volume resolvent decays exponentially in `d`, with constants depending
only on `K` and `|Im z|`, uniformly in the finite set `Λ` and the potential `v`:
`|G_Λ(z; x, y)| ≤ (2/η) exp(-μ d(x, y))`, `μ = log (1 + η / (2 (K + 1)))`, `η = |Im z|`.

Motivation: (1.28) and Appendix B of Fröhlich–Spencer (1983), Fröhlich–Spencer (1983).
-/
@[expose] public section
open Matrix
namespace FroehlichSpencer.Infra
section Helpers
end Helpers
section Core
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}
end Core
section Main
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}
end Main
end FroehlichSpencer.Infra
