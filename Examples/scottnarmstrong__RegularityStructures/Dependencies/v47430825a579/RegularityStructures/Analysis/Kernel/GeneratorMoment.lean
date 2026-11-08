/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.GeneratorLip
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Convergence and boundedness of `Q_v φ`

* `abs_apply_sub_le`: `|Q_v φ(z) - φ(z)| ≤ C v^{1/4}`;
* `abs_apply_le`: `|Q_v g(z)| ≤ M₀ sup|g|`.
-/
public section
open MeasureTheory Filter Topology Real
open scoped ContDiff
namespace RegularityStructures
end RegularityStructures
end
