-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientPotential
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientRemainder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Endgame.WeakPressureSlice
set_option autoImplicit false
set_option warningAsError true
/-! # The selected weak pressure gradient on one slice

Display (3.5) of the pressure-gradient section estimates the weak spatial
gradient of a pressure slice after the local decomposition
`p = p₁ + p_har + (p₇ + p₈)`.  The first summand is a coordinate sum of
Newtonian derivative potentials of a divergence-form source `V` and is
differentiated by the Calderón–Zygmund selection; the second is smooth on the
inner ball and is differentiated classically; the third is differentiated by
its own potential identities.

This file performs the assembly: it produces one `Vec3`-valued slice field
whose coordinates are locally integrable, which lies in `L^{6/5}` on the inner
set, which is the coordinate weak gradient of the pressure slice there, and
whose coordinate norms obey the three-term bound of display (3.5).
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4
