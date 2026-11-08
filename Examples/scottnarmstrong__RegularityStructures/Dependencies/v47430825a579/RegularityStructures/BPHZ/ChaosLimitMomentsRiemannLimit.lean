/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.ChaosLimitMomentsRiemann
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Pathwise convergence of the sampled tested fields

If `ψ(ω, ·)` is continuous, `S` is compact, the test function `g` is supported in `S`, the kernel
`k(y, ·)` is supported in `S` whenever `g y ≠ 0` and `∫ |k(y, w)| dw ≤ L`, then for sampling maps
`πₙ` with values in `S` and `πₙ x → x` on `S`, the sampled tested fields `chaosIntegral … (πₙ) ω`
converge to `chaosIntegral … id ω` (dominated convergence, twice).
-/
public section
open MeasureTheory Filter Topology
namespace RegularityStructures
variable {Ω : Type*}
end RegularityStructures
end
