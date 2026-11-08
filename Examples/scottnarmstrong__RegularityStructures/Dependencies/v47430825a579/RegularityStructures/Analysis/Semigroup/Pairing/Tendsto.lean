/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Semigroup.Pairing.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Existence of the pairing

`LocalData.exists_tendsto_integral`: `s ↦ ∫ Λ_s φ` has a limit as `s ↓ 0` (Cauchy criterion
from `LocalData.abs_integral_sub_le`, since the primitive `incrBound` tends to `0`).
-/
public section
open MeasureTheory Filter
open scoped Topology
namespace RegularityStructures.RegularisingSemigroup
variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {K : RegularisingSemigroup E μ}
end RegularityStructures.RegularisingSemigroup
end
