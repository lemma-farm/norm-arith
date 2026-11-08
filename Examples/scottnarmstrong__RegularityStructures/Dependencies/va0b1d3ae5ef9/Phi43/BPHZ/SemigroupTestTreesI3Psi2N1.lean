/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.SemigroupTestTreesI3PsiChain
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va0b1d3ae5ef9.Phi43.BPHZ.TreeI3Psi2DiagramN1Bound
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# The diagram `N₁` of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

`i3Psi2N1_bound_global`: for kernels `K, Q` as in `i3PsiPairing_bound_uniform`, arbitrary `z, z'`
(with `z, z', z - z'` away from the origin) and `D` bounding `s(z' - w)` on the slab
`|w.1| ≤ |z.1| + 1`, `|∫∫ N₁| ≤ C D^δ S_{1+δ}(z, z')`.  This is the proof of
`i3Psi2N1_bound_uniform` with the pointwise majorant `abs_i3Psi2N1_le` (which uses `s(z), s(z') ≤ 1`
only to bound `s(w - z') ≤ 3`) replaced by `abs_i3Psi2N1_le_global`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
