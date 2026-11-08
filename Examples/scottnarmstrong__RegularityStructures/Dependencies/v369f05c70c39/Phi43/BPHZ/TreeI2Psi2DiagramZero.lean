/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v369f05c70c39.Phi43.BPHZ.TreeI2Psi2DiagramPair
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chaos-`0` part of the tree `I(Ψ²) Ψ²`

[Hai14, (10.39)-(10.42)]: the chaos-`0` component is `-2 ∫ K(x - w) Q(w - y)² dw`, and
`K * Q²` is of order `-3 - 2 + 5 = 0`, so it is `≲ s(y - x)^(-δ)` for every `δ > 0`.
We prove it for `K`, `Q` as in the kernel calculus (`|K| ≤ B s^(-3)`, time support `|t| ≤ 1`,
`|Q| ≤ B s^(-1)`), for `|y₀ - x₀| ≤ 1`: `|∫ K(x - w) Q(w - y)²| ≤ C B³ s(y - x)^(-δ)`.  The borderline
total order `5` is handled by weakening `s^(-2)` to `3^δ s^(-2-δ)` on the support.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
