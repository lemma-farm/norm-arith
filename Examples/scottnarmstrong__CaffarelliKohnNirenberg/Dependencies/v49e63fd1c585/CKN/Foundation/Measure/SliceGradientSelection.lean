-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceGradientBumps
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceMollifierIdentity
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceProductMeasurability
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Statements.SpatialPartial
set_option autoImplicit false
set_option warningAsError true
/-!
# A jointly measurable space-time weak gradient from slice-wise weak gradients

Lemma `lem:delta-p` of the paper produces, for almost every time `t`, a spatial
weak derivative of the pressure slice `p (·, t)` on a ball `B`.  Nothing in that
statement says that the family of slice derivatives can be chosen jointly
measurable in space and time, and the almost-everywhere uniqueness of a weak
derivative pins each slice down only up to a null set of its own.  The theorems
below supply the missing selection.

The construction is a mollification.  With `φ n` the normalized bump of outer
radius `sliceRadius n` and inner radius half of that, the function

`G n (x, t) = ∫ y, (∂ₖ φ n) y * p (x - y, t) dy`

is an explicit integral of a jointly measurable integrand, hence jointly
measurable; and for each good time `t` and each `x` whose closed
`sliceRadius n`-ball stays inside the domain, the defining integration-by-parts
identity of `HasWeakPartialDerivOn` turns it into the mollification of the slice
derivative at `x`.  Mathlib's almost-everywhere convergence of mollifications
(External Input `ext:mollify`) then makes `G n (x, t)` converge to the slice
derivative at `x` for almost every `x`, so the pointwise limit

`Dp z = limUnder atTop (fun n => G n z)`

is a single space-time function that restricts to a weak derivative on almost
every slice.  The limit is `Filter.limUnder`, whose junk value off the
convergence set is harmless: every conclusion is stated almost everywhere on the
inner box.

The identity in the last conclusion is first proved in its iterated form
`∫ t in J, ∫ x in B'`, which needs no integrability of `Dp` at all;
`setIntegral_prod_eq_of_iterated` upgrades it to an integral over the product
box once both integrands are integrable there.

The data is truncated to an intermediate open set `W` with
`closure B' ⊆ W ⊆ closure W ⊆ B` before it is mollified, so that the truncated
slices are globally integrable and Mathlib's convergence theorem applies; only
the conclusions on `B'` are used.

Space-time points use the ordinary product space `Vec3 × ℝ` of docs/DESIGN_NOTES.md, the
carrier on which `spatialPartial` and `spaceTimeTestFunction` are stated.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology ENNReal
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end
