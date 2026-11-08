/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module
public import Examples.CoolRmal__falconer_packing.Dependencies.v8afd69a62295.FalconerPacking.BallOverlap
set_option autoImplicit false
/-!
# Measures formed from selected tube weights

A selected test at one child controls all enlarged children meeting a common rectangle.
The overlap loss is counted once, before the normalized averaging measures are inserted.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open Classical
namespace FalconerPacking
end FalconerPacking
