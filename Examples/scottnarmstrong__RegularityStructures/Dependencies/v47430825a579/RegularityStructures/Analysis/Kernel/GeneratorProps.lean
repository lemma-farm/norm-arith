/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Semigroup.Pairing.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Structural properties of the auxiliary semigroup

`parabolicSemigroup` is symmetric (the kernel is even), `scaleDist` is a metric-like size
(`IsMetricScale`), and the kernel is jointly measurable in `(t, x, y)`
(`IsJointMeasurable`), which is the form of measurability needed for Fubini in the time variable.
-/
public section
open MeasureTheory Real
namespace RegularityStructures
end RegularityStructures
end
