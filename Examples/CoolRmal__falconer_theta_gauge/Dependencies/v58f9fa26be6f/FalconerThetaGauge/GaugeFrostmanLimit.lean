/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeFrostmanMeasure
public import Mathlib
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Support
set_option autoImplicit false
/-!
# Weak compactness for the finite Frostman measures

Adapted from `FalconerPacking.WeakLimit` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/WeakLimit.lean

Probability measures carried by one compact planar set form a compact set for the weak topology.
Consequently every sequence of the normalized atomic Frostman measures has a weakly convergent
subsequence whose limit is still carried by the same compact set.
-/
@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped ENNReal
namespace FalconerThetaGauge.GaugeFrostman
end FalconerThetaGauge.GaugeFrostman
namespace FalconerThetaGauge
end FalconerThetaGauge
