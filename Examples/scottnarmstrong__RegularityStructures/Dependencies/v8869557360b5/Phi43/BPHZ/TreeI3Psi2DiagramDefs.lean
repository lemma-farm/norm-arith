/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiPowers
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The abstract covariance of the tree `I(Ψ³)Ψ²`

For a kernel `K` (the singular kernel) and a covariance `Q` (a mollified two-point function)
write `δK(z, w) = K(z - w) - K(-w)` (base point `0`).  The covariance of the field
`(Π̂^ε_0 τ)(z) = (δK ∗ :Ψ³:)(z) :Ψ²:(z) - 3 C₂ Ψ(z)`, `τ = I(Ψ³)Ψ²`, of `Phi43.BPHZ.TreeI3Psi2Field*`
(`hairerI3Psi2Field_integral_mul`, `hairerI3Psi2Cov`) is, at a single scale, the expression
`i3Psi2Cov K Q c z z'`, with `c = C₂` and the chaos-`5`, `3`, `1` kernels
`χ₅, χ₃, χ₁` of the product of two Wick cubes and two Wick squares evaluated at the points
`(w, z, w', z')`, the cross terms with the counterterm `-3 C₂ Ψ`, and the term `9 C₂² Q(z - z')`.
The entries are `c₀₂ = Q(w - w')`, `c₀₃ = Q(w - z')`, `c₁₂ = Q(z - w')`, `c₁₃ = Q(z - z')`,
`c₀₁ = Q(w - z)`, `c₂₃ = Q(w' - z')`, exactly as in `hairerI3Psi2Chaos5/3/1`.

Source: [Hai14] = arXiv:1303.5113v4, p. 170--171.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
