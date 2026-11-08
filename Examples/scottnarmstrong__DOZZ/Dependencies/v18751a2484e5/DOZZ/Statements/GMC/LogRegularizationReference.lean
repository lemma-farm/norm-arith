/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v18751a2484e5.DOZZ.Statements.GMC.RegularizedCoulombMass
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.logRegularizationReference`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- Reference measure with density `dens` on the chart `U`. -/
noncomputable def logRegularizationReference (U : Set ℂ) (dens : ℂ → ℝ) : Measure ℂ :=
  (volume.restrict U).withDensity (fun x => ENNReal.ofReal (dens x))
end DOZZ
