/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.TreeI2Psi2DiagramMultiBasic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v31d01570c762.Phi43.BPHZ.TreeI2Psi2DiagramPair
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The principal pairing and the product pairings with general exponents

For `A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')`, `r = s(y - x)`,
`r' = s(y' - x)`, `d = s(y - y')`, and pure singular weights:

* `i2Psi2LintBound_diag_sq`: `∫∫ |A| |A'| s(w' - w)^(-e) ≲ B² r^γ r'^γ'`;
* `i2Psi2LintBound_diag_prod_single`: `(∫ |A| s(y' - w)^(-e₁)) (∫ |A'| s(y - w')^(-e₂))`;
* `i2Psi2LintBound_diag_prod_pair`: the product of two pair integrals
  `(∫ |A| s(y - w)^(-e₁) s(y' - w)^(-e₂)) (∫ |A'| s(y' - w')^(-e₃) s(y - w')^(-e₄))`.

They generalise `i2Psi2LintBound_chaos4_sq`, `_chaos4_prod` and `_chaos2_prod` to free exponents.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
