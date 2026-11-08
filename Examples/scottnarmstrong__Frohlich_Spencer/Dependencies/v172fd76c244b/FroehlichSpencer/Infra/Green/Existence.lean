/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.APriori
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Green.CombesThomas
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Existence, uniqueness and finite-volume approximation of the `ℓ²` solution

For the pointwise equation `∑' w, a x w * ψ w + (v x - z) * ψ x = δ_y x` (generic: a Hermitian
kernel `a` of finite row support and bounded row sums, an arbitrary real potential `v`,
`Im z ≠ 0`) we prove: existence of a square-summable solution for countable index type (by
pointwise compactness of the finite-volume columns) and, with uniqueness from
`FroehlichSpencer.Infra.Green.APriori`, existence and uniqueness; convergence of the finite-volume
columns to any `ℓ²` solution (along the directed set of finite sets, uniformly, and along any
sequence eventually containing every point); Combes–Thomas decay of the solution; and the symmetry
`G(z; x, y) = conj G(conj z; y, x)`.

Motivation: Fröhlich–Spencer (1983), (1.4), (1.29),
Fröhlich–Spencer (1983).

No Green function is defined here.
-/
@[expose] public section
open Matrix Filter Topology
namespace FroehlichSpencer.Infra
section Helpers
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}
end Helpers
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}
section Existence
end Existence
end FroehlichSpencer.Infra
