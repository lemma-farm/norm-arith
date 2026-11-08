-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Harmonic.InteriorDisplays
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Cutoff.BallTopology
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Sobolev.Cutoff.NormTriangle
set_option autoImplicit false
set_option warningAsError true
/-!
# The interior supremum bound for weakly harmonic `L^{3/2}` functions

This file proves the first display `eq:harm-sup` of `lem:harmonic-interior` in
`paper/ckn.tex`: for a function `h` that is weakly harmonic on the ball
`B_ρ(x₀)` and lies in `L^{3/2}(B_ρ(x₀))`,

  `‖h‖_{L^∞(B_{3ρ/4}(x₀))} ≤ C₁₇ ρ^{-2} ‖h‖_{L^{3/2}(B_ρ(x₀))}`,

with an absolute constant `C₁₇`.

The established interior displays `weak_harmonic_interior_displays` produce a
continuously differentiable representative of `h` on the half ball together
with a pointwise bound for that representative on the three-quarter ball.  The
essential supremum of `h` itself on the three-quarter ball is obtained here by
applying those displays at every centre `y ∈ B_{3ρ/4}(x₀)` on the ball
`B_{ρ/4}(y) ⊆ B_ρ(x₀)`, which identifies `h` with its representative almost
everywhere on `B_{ρ/8}(y)`, and by localizing the resulting null sets: a set
that is null in a neighbourhood of each of its points is null in a
second-countable space.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal NNReal Topology
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
end CKN.Foundation.Heat
