/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3PsiChainBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Symmetrisation of the exponents `s(a - b)^(-δ)`

For the three points `z`, `z'`, `0`, every ordered pair `(a, b)` gives
`s(a - b)^(-δ) ≤ 2 (s(z - z')^(-δ) + s(z - 0)^(-δ) + s(z' - 0)^(-δ))`, using
`s(-x) ≤ 2 s(x)` and that `s(a - a) = 0`.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
