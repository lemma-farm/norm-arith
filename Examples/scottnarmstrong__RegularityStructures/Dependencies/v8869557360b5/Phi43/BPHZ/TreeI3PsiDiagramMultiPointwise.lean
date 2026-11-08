/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiDiagramMultiChain
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiDiagramMultiPrincipal
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiDiagramSlab
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Pointwise domination by the chain and principal majorants

For the kernel `K` of order `-3`, supported in `|t| ≤ 1`, and `s(z), s(z') ≤ 1`:

* `abs_dK_dK_chain_le`: `|δK(z,w)| |δK(z',v)| · s_{1+α}(u,w) s(w-v)^(-(2+β₀)) s_{1+γ}(u',v)` is bounded
  by `B² 3^δ` times `i3PsiChainMajorant α (β₀ + δ) γ`;
* `abs_dK_dK_principal_le`: `|δK(z,w)| |δK(z',v)| · s_{3+τ}(w,v)` is bounded by
  `12 B² s(z')^θ` times `i3PsiPrincipalMajorant θ τ`.

`singularPow_flip_le` converts `s(w - u)^(-a)` to the centred power `s_a(u, w)`.
-/
public section
open MeasureTheory Set
namespace RegularityStructures
end RegularityStructures
end
