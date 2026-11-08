/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.SingularConvolution
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Stochastic.ConstantsComparisonDefinitions
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Singular bounds for Hairer's mollified covariance

For `K_ε = hairerMollifiedKernel N ρ ε` and `Q_ε(z) = ∫ K_ε(z + w) K_ε(w) dw`, we prove
`|Q_ε z| ≲ s(z)⁻¹` (via the convolution estimate of `SingularConvolution`, [Hai14, Lemma 10.14])
and the uniform bound `|Q_ε z| ≲ (s(z) + ε)⁻¹`, valid also at `s z = 0`.
-/
public section
open MeasureTheory
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
