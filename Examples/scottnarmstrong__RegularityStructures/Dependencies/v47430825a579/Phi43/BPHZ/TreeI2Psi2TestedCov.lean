/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2FieldCov
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramChaosFour
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramChaosTwo
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2DiagramZero
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.HairerCovarianceBounds
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.HairerKernelIncrementTorus
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.PsiGaussianVectorContinuous
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonC2Bounds
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The pointwise covariance bound for the field of `I(Ψ²) Ψ²`

By `hairerI2Psi2Field_integral_mul` the covariance `E[F_x(y) F_x(ȳ)]` is the sum of the chaos-`4`
integral, the chaos-`2` integral and the product of the two means.  With `K = hairerKernelTorus N`
and `Q = hairerCovariance N ρ ε` these are exactly the integrals bounded by
`integrable_and_abs_integral_chaos4_le`, `_chaos2_le` and `_chaos0_le`; the constant `B` in their
hypotheses is independent of `ε ∈ (0, 1]` and `x` (`hairerCovariance_abs_le`).  The result is
[Hai14, (10.39)-(10.42)]: for `s(y - x), s(ȳ - x) ≤ 1`, with `d = s(y - ȳ)`, `r = s(y - x)`,
`r' = s(ȳ - x)`,
`|E[F_x(y) F_x(ȳ)]| ≤ C (d^(-δ) + d^(-2) (r^(2-δ) + r'^(2-δ)) + r^a r'^a d^(-1) +
  r^(-2δ) + r'^(-2δ))`.
-/
public section
open MeasureTheory
universe u
namespace RegularityStructures.Phi43
open RegularityStructures
end RegularityStructures.Phi43
end
