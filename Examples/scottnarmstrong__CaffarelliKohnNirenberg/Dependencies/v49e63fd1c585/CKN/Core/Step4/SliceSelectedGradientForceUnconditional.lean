-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientAssembly
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientScaling
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientForceP8
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientForceSlices
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.PkBoundsUnconditionalConstants
set_option autoImplicit false
set_option warningAsError true
/-! # The force potentials of a slice carry a weak gradient, with no condition on `div f`

The last two summands `p₇ + p₈` of the local pressure decomposition `eq:pk`
are the force potentials.  The class `def:sws` imposes no condition on the
spatial divergence of the force, so display (3.5) of the pressure-gradient
section must carry them: they do not cancel in general.

The first, `p₇ = -∑ⱼ ∂ⱼN * (η fⱼ)`, is a coordinate sum of Newtonian
derivative potentials of the cut-off force, which is exactly the shape the
Calderón–Zygmund selection differentiates, with the `L^{6/5}` bound of that
selection.  The second, `p₈ = -∑ⱼ N * (∂ⱼη fⱼ)`, has its density carried by
the cutoff annulus, hence is `C¹` on the inner ball `B_{ρ/2}(x₀)` with the
far-field gradient bound of `eq:har-Ck` at order one; its classical gradient
there is its weak gradient.  Adding the two produces one slice field, in
`L^{6/5}` of the inner ball with the `ρ^{-1/2}` weight of display (3.5).
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4
