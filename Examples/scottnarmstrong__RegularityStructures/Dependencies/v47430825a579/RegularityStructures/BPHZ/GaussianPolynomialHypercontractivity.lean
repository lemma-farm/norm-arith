/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianPolynomialEnergyStep
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Dimension-free equivalence of moments for Gaussian polynomials

For every `m` and `k` there is a constant `A` such that for all `n` and every polynomial `f` in `n`
variables of total degree at most `m`,
`E[f^(2^(k+1))] ≤ A (E[f²])^(2^k)` under the standard Gaussian measure
(`exists_integral_eval_pow_le_of_totalDegree_le`).

The proof uses the tower `E_j = ∑ |∂^j f|²` of iterated gradient energies, which satisfies
`E_j = 0` for `j > m`, `E[E_j] ≤ m^j E[f²]` (reverse Poincaré), and `M_j = E[E_j^q] ≤ c + β M_{j+1}`
for `q = 2^(k+1)` (one step of the dyadic spectral gap), so a downward induction in `j` bounds
`M_1 ≤ A_m (E f²)^q`.  The dyadic spectral gap for `f` itself then bounds the `2q`-th moment of
`f - E f` by `M_1`.
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
