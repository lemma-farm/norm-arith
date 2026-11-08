-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.Density
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.BilinearForms
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.TimeHolder
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Parabolic.FourierGalerkin.CutoffNesting
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Equation-derived weak time moduli

Testing each larger-cutoff ODE by an embedded lower-cutoff Fourier vector yields a common
one-half-Hölder modulus, with the uniform spatial gradient energy supplying the time Cauchy bound.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance equationModulusMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance equationModulusMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance equationModulusProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance equationModulusTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
end AVenhance.Infra.Parabolic.FourierGalerkin
end
