-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Ergodic.HMinusOne
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Finite spectral support for the H⁻¹ ergodic split

These helpers sit above the shared torus Fourier API.  They do not define a
new Fourier transform or integration convention. -/
@[expose] public section
namespace AVenhance.Infra.Ergodic
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus
noncomputable section
local instance avInfraErgodicHMinusOneSpectralMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicHMinusOneSpectralMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicHMinusOneSpectralIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance] Measure.Subtype.measureSpace
end
end AVenhance.Infra.Ergodic
