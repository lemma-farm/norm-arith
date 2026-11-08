/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.Scaling
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Decomposition.ScalingDeriv
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Derivative bounds for the heat shells

`|D₁^k D₂^l K_n(x, y)| ≤ C 2^{(5 - 2 + |l|_𝔰 + |k|_𝔰) n}` for `K_n(x, y) = heatShell n (x - y)`
[Hai14, (5.4)] with `β = 2`.
-/
public section
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
