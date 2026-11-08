/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramMultiTriple
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The monomials of the difference bound for `I(Ψ²) Ψ²`

Throughout `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`, `r = s(y - x)`, `r' = s(y' - x)`, `d = s(y - y')`,
`η = 2θ + δ`, and `F = i2Psi2DiffF θ δ r r' d`.  Each monomial of the second difference of the
chaos kernels is a product of four covariance weights, one of which has its exponent raised by `2θ`
(`TreeI2Psi2DifferencePointwise`).  Its diagram integral is bounded by `C B² F`:

* `i2Psi2LintBound_diff_sq_inner`, `_sq_outer`: `s(w' - w)^(-(2+2θ)) d^(-2)`, `s(w' - w)^(-2)
  d^(-(2+2θ))`;
* `i2Psi2LintBound_diff_prod_left`, `_prod_right`: the product pairings with a raised exponent;
* `i2Psi2LintBound_diff_cross_inner`: the cross pairing with a raised exponent among the three
  integrated weights, times `d^(-1)`;
* `i2Psi2LintBound_diff_cross_outer`: the cross pairing times `d^(-(1+2θ))`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
