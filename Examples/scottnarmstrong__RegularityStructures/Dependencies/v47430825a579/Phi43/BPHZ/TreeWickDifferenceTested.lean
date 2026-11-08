/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeWickDifferenceCov
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreePsiDifference
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.PsiGaussianVector
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Measurability of the cross covariance

`measurable_hairerCrossCovariance`: the cross covariance `Q_{ε,ε'}` of the fields `Ψ_ε`, `Ψ_ε'`
of two regularised noises of the same white noise is measurable. It enters the second moments of
the tested differences of Wick powers at two scales [Hai14, (10.3) for `τ = Ψ²`, `Ψ³`].
-/
public section
open MeasureTheory
universe u
namespace RegularityStructures.Phi43
open RegularityStructures
end RegularityStructures.Phi43
end
