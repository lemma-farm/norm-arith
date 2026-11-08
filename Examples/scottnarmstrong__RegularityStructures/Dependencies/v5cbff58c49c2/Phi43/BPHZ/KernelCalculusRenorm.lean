/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v5cbff58c49c2.Phi43.BPHZ.KernelCalculusRenormIntegrals
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v5cbff58c49c2.Phi43.BPHZ.KernelCalculusRenormPointwise
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The renormalised convolution

[Hai14, Lemma 10.16 (ii)]: for `f₁` of order `-a₁` with `5 < a₁ < 6`, and `f₂` of order `-a₂`
with the increment bound `|f₂(u + h) - f₂ u| ≤ B₂ s(h) s(u)^(-a₂-1)` for `s h ≤ s u / 2`, and
`a₁ + a₂ < 10`, the renormalised convolution `∫ f₁(x) (f₂(z - x) - f₂ z) dx` is bounded by
`C B₁ B₂ s(z)^(5-a₁-a₂)` (`= s(z)^(min 0 (5-a₁-a₂))`, as `a₁ + a₂ > 5`).

The endpoint `a₁ = 5` is excluded: there the bound fails by a logarithm, `f₁ = s^(-5) 1_{s ≤ 1}`
and `f₂ = s^(-a₂)` with `a₂ > 0` giving `ρ^(-a₂) log(1/ρ)`.  No time-support hypotheses are
needed, since all majorants are integrable on `SpaceTime`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.16, p. 156.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
