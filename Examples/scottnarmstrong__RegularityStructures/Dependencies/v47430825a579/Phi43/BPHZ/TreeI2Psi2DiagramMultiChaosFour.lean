/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramMultiTerms2
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Chaos `4` of the difference bound for `I(Ψ²) Ψ²`

The second difference of the chaos-`4` kernel is dominated by the sum `i2Psi2Maj4` of eight
monomials, each a product of four covariance weights with the exponent of exactly one of them
raised by `2θ` (in the notation `c₀₂ = s(w' - w)`, `c₀₃ = s(y' - w)`, `c₁₂ = s(y - w')`,
`c₁₃ = d = s(y - y')`):

`c₀₂^(-(2+2θ)) c₁₃^(-2) + c₀₂^(-2) c₁₃^(-(2+2θ)) + c₀₃^(-(2+2θ)) c₁₂^(-2) +
 c₀₃^(-2) c₁₂^(-(2+2θ)) + (c₀₃^(-(1+2θ)) c₀₂^(-1) c₁₂^(-1) + c₀₃^(-1) c₀₂^(-(1+2θ)) c₁₂^(-1) +
 c₀₃^(-1) c₀₂^(-1) c₁₂^(-(1+2θ))) c₁₃^(-1) + c₀₃^(-1) c₀₂^(-1) c₁₂^(-1) c₁₃^(-(1+2θ))`.

`i2Psi2LintBound_diff_chaos4`: `∫∫ |A| |A'| (that sum) ≲ B² F` with the majorant
`F = i2Psi2DiffF θ δ r r' d` (the block of eight terms is [Hai14, (10.3)] for the chaos-`4` part of
`τ = I(Ψ²) Ψ²`).
-/
@[expose] public section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
end RegularityStructures
end
