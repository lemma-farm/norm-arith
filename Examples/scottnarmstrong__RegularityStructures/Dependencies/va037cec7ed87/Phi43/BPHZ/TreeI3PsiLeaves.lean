/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiPowers
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Integrable majorants with an explicit integral bound

`SingularIntLe f X` records that `f` is integrable on space-time with `∫ f ≤ X`.  Using it we
package the integral estimates of products of centred parabolic powers that are needed for the
diagram bounds of the tree `I(Ψ³)Ψ`:

* two powers of total order `5 + η > 5` (from `integrable_and_integral_singularPow_mul_le`);
* three powers of total order `5 + η`, two of which have total order `< 5`;
* two powers of total order `< 5`, restricted to the time slab `|t| ≤ 2`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14 and (10.37a).
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
