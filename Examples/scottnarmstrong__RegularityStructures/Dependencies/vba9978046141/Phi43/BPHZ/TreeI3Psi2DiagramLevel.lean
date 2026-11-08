/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3PsiLeaves
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3PsiTwoLevel
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3Psi2DiagramBasic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3PsiChain
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Two-level majorants with a `SingularIntLe` inner integral

If `|F w v| ≤ m w * g w v` with `∫ g w ≤ V w` (for almost every `w`) and `m V` integrable with
integral at most `X`, then `F` is integrable on the product and its iterated integral is at most
`X` in absolute value.  This packages `integrable_prod_of_two_level` in the form in which the
diagram bounds for `I(Ψ³)Ψ²` use it.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
