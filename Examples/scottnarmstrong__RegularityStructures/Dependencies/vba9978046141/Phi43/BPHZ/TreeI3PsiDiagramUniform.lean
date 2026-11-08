/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3PsiDiagramSlab
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3PsiPrincipalBound
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The diagram bound for `I(Ψ³)Ψ`, uniform in the kernels

`i3PsiPairing_bound_uniform`: for `B ≥ 0`, `δ ∈ (0, 1/4]` there is a constant `C`, depending only on
`B, δ`, such that for **all** kernels `K, Q` satisfying the hypotheses of `i3PsiPairing_bound`
(except the time-support hypothesis on `Q`, which is not needed), the integrated diagram is bounded
as in `i3PsiPairing_bound`.  The uniformity in `(K, Q)` is what allows `Q = Q_ε` to vary with
`ε`.  The proofs are those of `i3PsiPrincipal_bound` and `i3PsiPairing_bound` with the order of the
quantifiers changed.

Source: [Hai14] = arXiv:1303.5113v4, (10.36)--(10.38), p. 167--168.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
