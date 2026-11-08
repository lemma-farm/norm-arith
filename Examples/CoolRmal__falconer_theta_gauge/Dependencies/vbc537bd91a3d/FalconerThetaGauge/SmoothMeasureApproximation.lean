/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.OrliczEnergyFourier
public import Mathlib
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Group.LIntegral
set_option autoImplicit false
/-!
# Smooth approximation of finite source measures

A compact smooth convolution kernel gives an actual smooth density. The corresponding
measure is the convolution of the source with the kernel measure, so probability kernels
decrease Fourier energy. These genuine convolution arguments adapt
`FalconerPacking.SmoothMeasureApproximation` (Yongxi Lin, Apache 2.0) at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/SmoothMeasureApproximation.lean
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped ENNReal ContDiff Convolution
namespace FalconerThetaGauge
def smoothBumpMeasure (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (φ.normed volume x))
instance smoothBumpMeasure.instIsProbabilityMeasure
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    IsProbabilityMeasure (smoothBumpMeasure φ) where
  measure_univ := by
    rw [smoothBumpMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
        (Filter.Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
end FalconerThetaGauge
