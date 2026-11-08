/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.GeneratorLimit
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic Lipschitz bound for compactly supported smooth functions

`|φ(y) - φ(z)| ≤ C ‖y - z‖_𝔰`: for `|y₀ - z₀| ≤ 1` the sup norm is dominated by `‖·‖_𝔰` and `φ`
is Lipschitz; otherwise `‖y - z‖_𝔰 ≥ 1` and `φ` is bounded.
-/
public section
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
