/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3Psi2DiagramMultiN2
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3Psi2DiagramMultiLevel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Bound for the weighted diagram `N₂` with general exponents

`i3Psi2N2Weighted_bound`: every measurable `F` dominated by
`Λ |δK(z, w)| |δK(z', v)| s(w - z)^(-(1+y₁)) s(w - z')^(-(1+y₂)) s(w - v)^(-(1+y₃))
s(v - z')^(-(1+y₄)) s(z - v)^(-(1+y₅))` is integrable on the product and
`|∫∫ F| ≤ Λ C S_{1+δ+y₁+⋯+y₅}(z, z')`.  The proof is that of the a-priori bound for `N₂` with the
exponents `(1 + ν₁, 1 + y₂, 1 + y₃, 4 + y₄, 1 + y₅)` in place of `(1 + δ, 1, 1, 4, 1)`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
