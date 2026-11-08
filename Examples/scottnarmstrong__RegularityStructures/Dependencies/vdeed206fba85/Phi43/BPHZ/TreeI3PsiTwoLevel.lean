/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.Phi43.BPHZ.TreeI3PsiSlab
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Two-level domination of a double integral

If `|F w w'| ≤ G w w'` where, for almost every `w`, `G w` is integrable with `∫ G w ≤ H w` and `H`
is integrable, then `F` is integrable on the product and the iterated integral of `F` is at most
`∫ H` in absolute value.  This is the integrability statement for the Wick-diagram integrands
(Fubini for the pairing `∫∫ δK δK Q ⋯`).
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
