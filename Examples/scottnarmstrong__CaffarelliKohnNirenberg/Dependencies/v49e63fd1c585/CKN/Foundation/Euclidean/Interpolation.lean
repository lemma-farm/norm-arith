-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.InterpolationBasic
set_option autoImplicit false
set_option warningAsError true
/-!
# Marcinkiewicz interpolation between weak `(1,1)` and strong `(2,2)`

For a sublinear operator `T` on functions `Vec3 → ℝ` that is of weak type
`(1,1)` with constant `A₁` and of strong type `(2,2)` with constant `A₂`, the
interpolation theorem `interpolation_weak11_strong22` gives the strong `(p,p)`
bound with the explicit constant `p · 2^p · (A₁/(p-1) + A₂²/(2-p))` for every
`1 < p < 2`.  The exponents `p = 3/2` and `p = 6/5` are recorded as corollaries.

The analytic ingredients — the distribution-function estimate obtained by
truncating at level `t/2`, and its layer-cake integral against the weight
`p t^{p-1}` — are in `InterpolationBasic.lean`.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
end CKN.Foundation.Euclidean
