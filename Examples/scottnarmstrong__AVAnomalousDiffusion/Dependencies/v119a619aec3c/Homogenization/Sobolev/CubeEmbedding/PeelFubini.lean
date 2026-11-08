-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
module
public import Mathlib
public import Mathlib.MeasureTheory.Integral.Prod
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.Homogenization.Ambient.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
open MeasureTheory Homogenization
/-!
# Coordinate-peeling Fubini on `Vec d`

Reusable slicing lemma: an integral over `Vec (n+1) = Fin (n+1) → ℝ` against
Lebesgue `volume` equals the iterated integral obtained by peeling off a chosen
coordinate `i` as the inner one-dimensional line integral (the remaining
coordinates outer).  The line through `z : Vec n` in direction `i` is
`t ↦ i.insertNth t z`.

This is the tool into which the single-face reflection transport feeds its
per-line one-dimensional integration by parts.
-/
noncomputable section
end
end Homogenization
