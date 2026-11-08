/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiChainBasic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiTwoLevel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The principal pairing of the tree `I(Ψ³)Ψ`

The double integral `∫∫ δK(z, w) δK(z', w̄) Q(w - w̄)³ dw dw̄` (the factor `δ²Q^{(3)}(z, z')` of
[Hai14, p. 167]) is absolutely integrable and bounded by `C s(z')^θ` for every `θ ∈ (0, 1)`,
provided `s(z) ≤ 1` and `s(z') ≤ 1`.  The Hölder gain `s(z')^θ` comes from the increment bound of
`K` (Lemma 10.18); the remaining convolution has total order `4 + θ < 5`, hence is bounded on the
time slab `|t| ≤ 2` carrying the support of `δK(z, ·)`.

Source: [Hai14] = arXiv:1303.5113v4, p. 167, last display.
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
