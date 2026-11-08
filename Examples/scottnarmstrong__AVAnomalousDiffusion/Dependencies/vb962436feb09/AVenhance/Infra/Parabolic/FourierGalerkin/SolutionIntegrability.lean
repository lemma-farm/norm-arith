-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarRepresentative
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDriftProduct
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integrability of the drift pairing at the synchronized limit
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open Homogenization
open scoped ENNReal RealInnerProductSpace
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance solutionIntegrabilityMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance solutionIntegrabilityProbabilityCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance solutionIntegrabilityProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
end AVenhance.Infra.Parabolic.FourierGalerkin
end
