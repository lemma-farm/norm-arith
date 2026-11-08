/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.GeneratorDiff
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.GeneratorProps
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The approximate identity: `∫ q_v(z - y) φ(y) dy → φ(z)` as `v ↓ 0`

`∫ q_v = 1`, `|φ(y) - φ(z)| ≤ C ‖y - z‖_𝔰` for `φ` smooth with compact support, and the first
moment bound `∫ |q_v(z - y)| ‖y - z‖_𝔰 dy ≤ M₁ v^{1/4}`.
-/
public section
open MeasureTheory Filter Topology Real
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
