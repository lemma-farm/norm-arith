/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.GeneratorStep
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Differentiating `v ↦ ∫ q_v(z - y) φ(y) dy` under the integral sign

For `v > 0` and `φ` continuous with compact support, `F(v) = ∫ q_v(z - y) φ(y) dy` has derivative
`∫ (∂_v q_v)(z - y) φ(y) dy`. The domination uses the time-derivative bound of
`RegularityStructures.Analysis.Kernel.TimeDeriv` and boundedness of the profile.
-/
public section
open MeasureTheory Filter Topology Real
open scoped ContDiff
namespace RegularityStructures
variable {φ : ParabolicSpace → ℝ}
end RegularityStructures
end
