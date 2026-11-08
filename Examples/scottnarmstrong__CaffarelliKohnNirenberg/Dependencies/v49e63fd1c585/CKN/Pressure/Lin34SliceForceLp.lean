-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.PotentialLocalLpP8
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PkBoundsP7Solution
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Cutoff
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.BallOrigin
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# The force potential `p₇ + p₈` is `L^{3/2}` on a.e. time slice

The decomposition `prop:pressure-decomposition`, grouped in `cor:CZ-harmonic`,
splits the local pressure into a Calderón–Zygmund part, a harmonic remainder,
and the force potentials `p₇` and `p₈` built from the cutoff `η` and the force `f` of a
suitable weak solution `def:sws`.  This file records the time-slice form of the force
estimate needed by the quantitative Hölder consumer `prop:lin34`: for almost every time in
the lower half of a parabolic cylinder, the sum `p₇ + p₈` is `L^{3/2}` on every round ball
of the spatial slice.

The proof combines three ingredients from
`CKN/Pressure/PkBoundsP7Solution.lean` and `CKN/Pressure/HarmonicRemainderForceTerms.lean`:
the a.e.-in-time slice data for the force, the `L^q` membership of the two families of
sources `η fⱼ` and `(∂ⱼ η) fⱼ`, and the local `L^{3/2}` theory of the Newtonian potentials
`CKN.Foundation.Euclidean.pressureP7_add_pressureP8_memLp_and_lpNorm_growth`.
-/
/-! ### Step 1: a.e. slice data for the force -/
end CKN
