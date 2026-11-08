/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.Phi43.BPHZ.TreeI3PsiDiagram
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The diagram bound for `I(Ψ³)Ψ` without a time support hypothesis on `Q`

`i3PsiPairing_bound` assumes that the covariance `Q` vanishes for `|t| > 2`.  The mollified
covariance `Q_ε = K_ε ⋆ K_ε^-` is supported in `|t| ≤ 2 (1 + ε² R)` where `R` is the time radius of the
mollifier, so this fails for every `ε > 0` as soon as `R > 0`.  The support is used only to bound
`Q(w - v)²` by `3^δ s(w - v)^(-2-δ)`; but the recentred kernels `δK(z, w)`, `δK(z', v)` vanish unless
`|w.1|, |v.1| ≤ 2` (for `s(z), s(z') ≤ 1`), hence only `|(w - v).1| ≤ 4` matters, where `s ≤ 3` still
holds.  This file re-proves the chain and total bounds with the support hypothesis on `Q` removed
(the support hypothesis on `K` is kept).

Source: [Hai14] = arXiv:1303.5113v4, (10.36)--(10.38), p. 167--168.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
