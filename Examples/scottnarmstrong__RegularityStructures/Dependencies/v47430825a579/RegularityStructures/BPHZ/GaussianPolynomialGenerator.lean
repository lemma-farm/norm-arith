/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianPolynomialIBP
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The Ornstein--Uhlenbeck generator on Gaussian polynomials

For polynomials in `n` variables, the Gaussian expectation `gaussExp p = ∫ eval x p dγ` is a linear
functional, and the Ornstein--Uhlenbeck generator is
`gaussGen f = ∑ i, (X i * ∂_i f - ∂_i ∂_i f)`.  Gaussian integration by parts gives the Dirichlet
form identity `∑ i, E[∂_i f ∂_i g] = E[f * gaussGen g]` (`sum_gaussExp_pderiv_mul_pderiv`), so
`gaussGen` is symmetric.  The Euler identity shows that `gaussGen f - (m + 1) f` has degree at most
`m` when `f` has degree at most `m + 1` (`totalDegree_gaussGen_sub_le`).
-/
@[expose] public noncomputable section
open MvPolynomial MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
public section
open MvPolynomial MeasureTheory
namespace RegularityStructures
variable {n : ℕ}
end RegularityStructures
end
