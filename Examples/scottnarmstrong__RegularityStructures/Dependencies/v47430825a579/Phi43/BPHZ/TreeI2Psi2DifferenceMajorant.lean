/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DifferenceAlgebra
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The diagram majorants of the second difference of the chaos kernels

For the kernel increments `A, A'` of `Phi43.BPHZ.TreeI2Psi2Field`, the eight-monomial majorants
`i2Psi2Maj4`, `i2Psi2Maj2` of the chaos-`4` and chaos-`2` parts of the covariance of the
difference of two fields of `I(Ψ²) Ψ²` are rewritten as `|A| |A'|` times the monomials
(`i2Psi2Maj4_eq`, `i2Psi2Maj2_eq`). They are used in `Phi43.BPHZ.TreeI2Psi2CrossMajorant`.
-/
public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
end RegularityStructures.Phi43
end
