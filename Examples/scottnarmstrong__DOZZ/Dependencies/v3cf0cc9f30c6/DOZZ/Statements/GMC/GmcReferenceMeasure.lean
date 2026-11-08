/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.GMC.FieldChaosMass
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.gmcReferenceMeasure`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- The deterministic reference measure `σ(dx)=|x|_+^{-4}d²x` of the equator GMC. See
[KRV, (Meps1) and (law)]. -/
noncomputable def gmcReferenceMeasure : Measure ℂ :=
  volume.withDensity (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)))
end DOZZ
