/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramCov
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The chaos-`4` monomials of the tree `I(Ψ²) Ψ²`: squared pairing

For `A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')` and a covariance `Q`
with `|Q| ≤ B s^(-1)`, the principal pairing
`∫∫ |A(w)| |A'(w')| Q(w - w')² dw dw' ≲ B⁴ s(y - x)^θ s(y' - x)^θ`, `θ = 1 - δ/2`
(`i2Psi2LintBound_chaos4_sq`): the inner integral is `≲ B³ r^θ (s(y - w')^(-θ) + s(x - w')^(-θ))`
(`i2Psi2LintBound_kernel_sub_two`, total order `5 + θ > 5`), and the outer one is bounded
(`i2Psi2LintBound_kernel_sub_slab`, total order `3 + θ + θ < 5`).  [Hai14, p. 169, after (10.39)].
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
