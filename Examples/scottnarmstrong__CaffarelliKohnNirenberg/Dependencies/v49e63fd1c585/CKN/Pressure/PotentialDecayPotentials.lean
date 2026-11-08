-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecay
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecayFarField
set_option autoImplicit false
set_option warningAsError true
/-!
# Linear growth of the pressure potentials

Combining the far-field decay of Newtonian potentials of compactly supported
data with the ball estimate for the radial weight `‖x‖ ^ (-3/2)` gives, for each
of the three potential shapes `N * g`, `∂ⱼN * g` and `∂ᵢ∂ⱼN * g`, exactly the
pair of hypotheses consumed by the Liouville theorem
`CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth`: local
`L^{3/2}` membership on every round ball about the origin, and a growth bound of
the form `C * (1 + ρ)`.  This is the decay-at-infinity input to the uniqueness
half of the Newtonian representation `ext:newtonian` of the paper.

The local `L^{3/2}` hypothesis near the origin is left to the consumer: for the
zeroth-order potential it follows from local integrability of the kernel, and for
the derivative potentials it is the Calderón–Zygmund bound.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
