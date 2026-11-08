/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianPolynomialEnergyTower
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianPolynomialLpGap
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# One step of the moment recursion for iterated gradient energies

Let `E = sqSum L` and `E' = sqSum (polyDerivs L)`, so that `|∇E|² ≤ 4 E E'` pointwise.  Writing
`q = 2^(k+1)` and `M = ∫ E^q dγ`, `M' = ∫ E'^q dγ`, the dyadic spectral gap for the polynomial `E`
together with Young's inequality `E^(q/2) E'^(q/2) ≤ E^q/(2t) + t E'^q/2` and the
convexity bound `(a + b)^q ≤ 2^(q-1) (a^q + b^q)` gives
`M ≤ 2 · 2^(q-1) μ^q + β M'`, where `μ` bounds the mean `∫ E dγ` and the constant `β` depends only
on `k` (`integral_pow_sqSum_le`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MvPolynomial MeasureTheory
namespace RegularityStructures
variable {n : ℕ}
end RegularityStructures
end
