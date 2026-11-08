/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v69d1dfa53e99.FroehlichSpencer.BKT.Surface.DensityDiameter
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The domain `D_j(ϱ)` of a charge density (KP (1.11)) -/
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
/-- `D_j(ϱ) = {ℓ ∈ Λ : dist (ℓ, j) < 2 d(ϱ)}` (KP (1.11), p. 5), the domain of `ϱ` with center `j`. -/
def Multigraph.densityDomain {V : Type u} {E : Type v} [Fintype V] (G : Multigraph V E)
    (ϱ : V → ℤ) (j : V) : Set V :=
  {ℓ | G.toSimpleGraph.dist ℓ j < 2 * G.densityDiameter ϱ}
end FroehlichSpencer.BKT
end
