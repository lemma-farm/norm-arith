/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.Phi43.BPHZ.TreeI2Psi2DiagramCross
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Single integrals of the kernel increment against two covariance weights

For `A(w) = K(y - w) - K(x - w)` and covariance weights `|c₁(w)| ≤ 2 B s(g₁ - w)^(-1)`,
`|c₂(w)| ≤ 2 B s(g₂ - w)^(-1)`, with `θ ∈ [0, 1)`, `ε ≥ 0`, `θ + ε > 0`:
`∫ |A| |c₁| |c₂| ≲ B³ s(y - x)^θ (s(y - g₂)^(-(θ+ε)) + s(x - g₂)^(-(θ+ε)) + 2 s(g₁ - g₂)^(-(θ+ε)))`
(`i2Psi2LintBound_cov_pair`).  The parameter `ε` weakens `s(g₂ - w)^(-1)` to
`3^ε s(g₂ - w)^(-1-ε)` on the time slab, which is how the borderline case `θ = 0` (total order
exactly `5`) is reached at the price of a power `ε`.  [Hai14, p. 170, (10.42) region].
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
