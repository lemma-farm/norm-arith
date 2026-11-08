/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramMultiChaosFour
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Chaos `2` of the difference bound for `I(Ψ²) Ψ²`

The second difference of the chaos-`2` kernel `16 c₀₁ c₂₃ (c₀₂ c₁₃ + c₀₃ c₁₂)` is dominated by the sum
`i2Psi2Maj2` of eight monomials, each a product of four covariance weights with the exponent of
exactly one raised by `2θ`: the four monomials of `c₀₁ c₂₃ c₀₂ c₁₃` (a cross pairing, times a power
of `d = c₁₃`) and the four of `c₀₁ c₂₃ c₀₃ c₁₂` (a product of two pair integrals).

`i2Psi2LintBound_diff_chaos2`: `∫∫ |A| |A'| (that sum) ≲ B² F`.
-/
@[expose] public section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
