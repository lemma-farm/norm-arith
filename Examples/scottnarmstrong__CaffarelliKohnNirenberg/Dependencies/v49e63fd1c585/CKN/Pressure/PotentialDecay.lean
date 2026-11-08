-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecayShell
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecayGeometry
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PotentialDecayGrowthSum
set_option autoImplicit false
set_option warningAsError true
/-!
# Linear growth of local `L^{3/2}` norms from decay at infinity

The Liouville step of the pressure identification needs its residual to satisfy
`‖r‖_{L^{3/2}(B_ρ)} ≤ C * (1 + ρ)` on the round balls `euclideanBall 0 ρ`.  This
file turns the pointwise decay `|h x| ≤ M * ‖x‖⁻¹` of a Newtonian potential of
compactly supported data into exactly that bound, with an explicit constant
built from the local norm near the origin and the universal ball constant
`invNormBallConstant` of `CKN.Pressure.PotentialDecayShell`.

This is the decay-at-infinity input to the uniqueness half of the Newtonian
representation `ext:newtonian` of the paper, whose proof applies Liouville's
theorem to a harmonic function that tends to zero in the `L^{3/2}` average
sense at infinity.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
