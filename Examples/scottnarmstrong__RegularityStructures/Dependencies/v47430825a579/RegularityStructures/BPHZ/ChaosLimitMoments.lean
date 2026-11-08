/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.ChaosLimitMomentsAE
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moment equivalence for almost sure limits of finite-chaos random variables

* `integral_pow_two_mul_le_of_ae_tendsto_cylindricalPolynomial`: if `Rₖ` are almost surely
  cylindrical polynomials of a white noise of degree at most `m`, `Rₖ → X` almost surely and
  `sup_k E Rₖ² < ∞`, then `E X^(2p) ≤ A * (E X²)^p`, with the constant `A = A(m, p)` of
  `integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`.
-/
public section
open MvPolynomial MeasureTheory Filter Topology
namespace RegularityStructures
universe u
end RegularityStructures
end
