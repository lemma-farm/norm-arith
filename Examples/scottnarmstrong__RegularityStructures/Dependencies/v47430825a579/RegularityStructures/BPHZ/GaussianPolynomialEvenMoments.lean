/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianPolynomialHypercontractivity
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Equivalence of all even moments for Gaussian polynomials

The dyadic moment equivalence `exists_integral_eval_pow_le_of_totalDegree_le` extends to every even
exponent `2 p`: for `p ≤ N = 2^k` and `y, s ≥ 0` one has `y^p s^(N-p) ≤ s^N + y^N`
(`pow_mul_pow_le_pow_add_pow`), and integrating with `y = f²` and `s = E f²` (or `s → 0` if
`E f² = 0`) bounds the `2p`-th moment by `(1 + A) (E f²)^p`.
-/
public section
open MvPolynomial MeasureTheory
namespace RegularityStructures
variable {n : ℕ}
end RegularityStructures
end
