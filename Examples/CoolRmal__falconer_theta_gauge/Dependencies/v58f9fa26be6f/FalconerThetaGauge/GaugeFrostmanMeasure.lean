/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeFrostman
public import Mathlib
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
set_option autoImplicit false
/-!
# Atomic gauge Frostman approximations

Adapted from `FalconerPacking.WeightMeasure`, `FalconerPacking.Restriction`,
and `FalconerPacking.OccupiedCubes` (original attribution preserved above),
`CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking

Positive finite gauge weights are normalized to genuine probability measures.
Compactness supplies occupied finite dyadic covers and selected atoms inside the
set. Cube estimates imply ball estimates with a factor of four.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge.GaugeFrostman
section CubeMass
variable {S : Finset (Fin 2 → ℤ)} {n : ℕ} {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}
end CubeMass
end FalconerThetaGauge.GaugeFrostman
