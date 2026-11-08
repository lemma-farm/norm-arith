/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiOuter
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiTwoLevel
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiSigma
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiSlab
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiChainBound
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Building blocks for the diagrams of `I(Ψ³)Ψ` with general exponents

* `TwoLevelLe G X`: a double-integral majorant `G` whose inner integrals are dominated by an
  integrable function of integral at most `X`; it yields integrability and a bound for every
  integrand dominated by `G`.
* the outer leaf and the inner integral of the chain diagram with the exponents
  `3`, `1 + α`, `1 + κ` (outer) and `4 + γ`, `2 + β` (inner), generalising the case
  `α = γ = 0`, `β = κ = δ` of `singularIntLe_outer_leaf` and `singularIntLe_inner`.

Source: [Hai14] = arXiv:1303.5113v4, (10.37a), Lemma 10.14, p. 167--168.
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
