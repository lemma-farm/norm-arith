-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Heat.SmoothClassical
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Heat.Analytic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
open MeasureTheory
open scoped ENNReal
noncomputable section
local instance avInfraHeatClassicalDerivativeMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraHeatClassicalDerivativeMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraHeatClassicalDerivativeIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
open AVenhance.Infra.Torus Homogenization
noncomputable section
namespace AVenhance.Infra.Heat
end AVenhance.Infra.Heat
