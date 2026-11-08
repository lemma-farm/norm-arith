/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3PsiChain
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Bound for the diagrams with a `Q²`-link

The chain integrand `i3PsiChain K Q z z' u u'` for `(u, u') ∈ {(z, z'), (z', z)}` is integrable on
`SpaceTime × SpaceTime` and its iterated integral is bounded by
`C (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167--168.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
