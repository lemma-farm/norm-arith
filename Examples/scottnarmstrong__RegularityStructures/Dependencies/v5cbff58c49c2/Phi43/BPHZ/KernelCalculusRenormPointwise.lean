/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v5cbff58c49c2.Phi43.BPHZ.KernelCalculusBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pointwise bound for the renormalised convolution

The integrand `f₁(x) (f₂(z - x) - f₂(z))` of [Hai14, Lemma 10.16 (ii)] is bounded, for
`s(z) = ρ`, by the sum of four integrable majorants: the near zone `s(x) ≤ ρ/4` (increment
bound), the tail of `f₁` against `f₂(z)`, the tail of `f₁` against `f₂(z - x)` away from the
singularity of `f₂`, and the neighbourhood of that singularity.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.16, p. 156.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
