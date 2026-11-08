/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.SingularConvolutionLayer
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Mass of a power singularity on a set of finite volume

For `0 < p < 5`, `lam > 0` and a measurable set `K` of finite volume, the integral of
`s(u - v)^(-p)` over `v ∈ K` is at most `80/(5-p) lam^(5-p) + lam^(-p) vol(K)`.  Near the
singularity (`s ≤ lam`) the layer-cake bound for `singularLocalWeight` applies; away from it the
weight is at most `lam^(-p)`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
