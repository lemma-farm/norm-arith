/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SmoothMeasureApproximation
public import Mathlib
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.IntegralConvolution
set_option autoImplicit false
/-!
# Weak convergence of the actual smoothed source probabilities

Normalized bumps form an approximate identity. Testing the measure convolution against
bounded continuous functions and applying dominated convergence recovers the original source.
These arguments adapt `FalconerPacking.SmoothProbabilityApproximation` (Yongxi Lin, Apache 2.0)
at commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/SmoothProbabilityApproximation.lean
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal ContDiff Convolution Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
