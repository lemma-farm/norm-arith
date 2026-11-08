-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.BallDisplays
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Cutoff.Ball
set_option autoImplicit false
set_option warningAsError true
/-!
# Volume scaling for the interior harmonic gradient display

The interior harmonic gradient display of the paper carries the factor
`ρ ^ (-3)` and is integrated over the half ball `B_{ρ/2}(x₀)`.  Its
`L^{5/6}`-type norm against the spatial measure therefore carries the half
ball volume raised to the power `5 / 6`.  This file records the resulting
scale bookkeeping: the product of the `ρ ^ (-3)` weight with
`|B_{ρ/2}(x₀)| ^ (5/6)` is bounded by `ρ ^ (-1/2)`, which is exactly the
factor appearing in display (3.5) of the paper.

The only input is the closed formula for the volume of a Euclidean ball in
three dimensions, `volume_vec3Ball_eq`.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4
