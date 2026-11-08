/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.Phi43.BPHZ.TreeI3PsiLeaves
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Two centred powers of total order `< 5` on a time slab

On the slab `|t| ≤ 2` the product of two centred parabolic powers of total order `a + b < 5`,
with centres of parabolic size at most `1`, is integrable with an integral bounded uniformly in
the centres.  This is the bounded case of [Hai14, Lemma 10.14] with an explicit time cut-off.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14, (10.37a).
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
