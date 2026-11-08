-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PkBoundsUnconditionalConstants
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# The Hölder steps of Proposition `prop:lin34`

Proposition `prop:lin34` of `paper/ckn.tex` turns a bound for an `L¹` integral
over a spatial ball into a bound for an `L^{3/2}` integral (display
`eq:lin34-pointwise`). The step is Hölder's inequality on the ball, with the
volume `(4π/3) ρ³` of the ball producing the prefactor. This file isolates that
analytic step.

* `lin34_ball_integral_le_rpow_three_halves` bounds `∫ g` over `vec3Ball x₀ ρ`
  by `(4π/3)^{1/3} ρ` times the `(2/3)`-power of the `L^{3/2}` integral of `g`.
-/
end CKN
