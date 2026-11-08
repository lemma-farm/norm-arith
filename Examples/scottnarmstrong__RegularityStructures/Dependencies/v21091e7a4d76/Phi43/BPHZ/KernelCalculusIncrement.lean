/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.Phi43.BPHZ.KernelCalculusBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Interpolated increments of singular kernels

[Hai14, Lemma 10.18] in increment form: if `|f u| ≤ B s(u)^(-a)` and
`|f(u + h) - f u| ≤ B s(h) s(u)^(-a-1)` whenever `s h ≤ s u / 2`, then for every
`θ ∈ [0,1]`
`|f z - f z'| ≤ 12 B s(z - z')^θ (s(z)^(-a-θ) + s(z')^(-a-θ))`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.18, p. 158.
-/
public section
namespace RegularityStructures
end RegularityStructures
end
