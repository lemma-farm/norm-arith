/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.GaugeLogEnergy
public import Mathlib
set_option autoImplicit false
/-!
# Separated compact pieces and their normalized measures

This file proves the geometric selection and normalization used at the start
of Proposition 5.6. It obtains two positive compact pieces from the constructed
gauge Frostman measure, rather than assuming the existence of separated pieces.
The restrictions retain the gauge bound and finite logarithmic critical energies.

The local positivity and normalization arguments are adapted from
`FalconerPacking.Extraction` and `FalconerPacking.Restriction` (original source
credits Yongxi Lin, Apache 2.0), at commit
`70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace FalconerThetaGauge
namespace GaugeSeparatedMeasures
/-- The literal normalized restriction; its nonzero finite mass is supplied at each use. -/
def normalizedRestrict (μ : Measure Plane) (K : Set Plane) : Measure Plane :=
  (μ K)⁻¹ • μ.restrict K
end GaugeSeparatedMeasures
end FalconerThetaGauge
