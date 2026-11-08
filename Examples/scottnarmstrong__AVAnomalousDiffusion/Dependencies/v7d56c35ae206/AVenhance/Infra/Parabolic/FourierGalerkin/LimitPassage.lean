-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.GalerkinSequence
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Parabolic.FourierGalerkin.FourierLimit
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The projected trace and the real Fourier limit

These lemmas identify the initial value of the concrete Galerkin paths with the real part of the
complex torus Fourier cutoff.  Combined with Parseval convergence, they supply the weak path
compactness theorem with the exact initial trace.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Homogenization
open scoped Topology RealInnerProductSpace
namespace AVenhance.Infra.Parabolic.FourierGalerkin
local instance limitPassageMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance limitPassageMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance limitPassageProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem LimitPassage.mFourierCoeff_congr_ae {f g : Torus → ℂ}
    (hfg : f =ᵐ[volume] g) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  simp [hx]
end AVenhance.Infra.Parabolic.FourierGalerkin
end
