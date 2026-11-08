/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiChainBound
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.Phi43.BPHZ.TreeI3PsiDiagramSlab
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The chain integral for an arbitrary integrand dominated by the chain majorant

`i3PsiChain_majorant_integral`: let `F` be any function such that, almost everywhere,
`|F w v| ≤ Λ (s₃(z, 0; w) s₁(u; w)) (s₄(z', 0, u'; v) s_{2+δ}(w; v))`, where `s_a(c; w) = s(c - w)^(-a)`.
Then `F` is integrable on the product and
`|∫∫ F| ≤ C Λ (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`, with `C` depending only on `δ`.
No assumption is made on the size of `z, z'`; the proof of `i3PsiChain_bound_uniform` after the
pointwise majorant is independent of the kernels.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
