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
# Regularity of finite-volume resolvent entries

The entries `resolventColumn a v Λ z y x` of the finite-volume resolvent are continuous and
measurable functions of the potential `v : X → ℝ` (product topology and product σ-algebra; they
depend only on `v|_Λ`), and continuous in `z` on `{Im z ≠ 0}`.

Motivation: finite-volume inputs
for the measurability of the infinite-volume Green function, cf.

Fröhlich–Spencer (1983),
Fröhlich–Spencer (1983).
-/
@[expose] public section
open Matrix
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}
end FroehlichSpencer.Infra
