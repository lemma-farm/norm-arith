-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.CZHarmonicCorollaryForceSlice
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PkBoundsCylinder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.DecompositionSWSBasic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SupportRestrict
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
/-!
# The slice data of the two force potentials of `eq:pk`

The local pressure decomposition `eq:pk` carries the force through the two potentials
`pressureP7 η f s` and `pressureP8 η f s` of `CKN.Pressure.DecompositionPotentials`,
whose densities on a time slice are `η y * f (y, s) j` and
`spatialDeriv η j y * f (y, s) j`.  Display (3.5) of the pressure-gradient section
differentiates these potentials on the inner ball of `η`, and therefore needs, on almost
every time slice of a suitable weak solution in the sense of `def:sws`: the `L^{6/5}`
membership and compact support of the first density, the integrability of the second
density, and an `L¹` bound for the second density in terms of the force on the ball.

The first fact is an immediate consequence of the compact support of the cutoff.  The
second and third transfer the slice membership of the force, supplied by
`sws_force_memLp_slice_ae`, to the two densities: the cutoff is bounded by one, so the
first density inherits every `L^p` bound of the force, while the derivative of the cutoff
is bounded by `cutoffGradientConstant / ρ`, which gives both the integrability of the
second density and its `L¹` estimate.
-/
end CKN.Core.Step4
