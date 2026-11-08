/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.Existence
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.FiniteVolumeRegularity
import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Infinite-volume solution: continuity in `z`, measurability in the potential

For families of square-summable solutions of `∑' w, a x w * ψ w + (v x - z) * ψ x = δ_y x`
(generic Hermitian kernel of finite row support and bounded row sums) we prove Lipschitz dependence
on `z` in `ℓ²`, continuity of `z ↦ ψ_z(x)` on `{Im z ≠ 0}`, and measurability of `v ↦ ψ_v(x)` for
the product σ-algebra on `X → ℝ` (countable `X`).

No Green function is defined here.

Motivation: Fröhlich–Spencer (1983), (1.4), Fröhlich–Spencer (1983).
-/
@[expose] public section
open Filter Topology
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}
end FroehlichSpencer.Infra
