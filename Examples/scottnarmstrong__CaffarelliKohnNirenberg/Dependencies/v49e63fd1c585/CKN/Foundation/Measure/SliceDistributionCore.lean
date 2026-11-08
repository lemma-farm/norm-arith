-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceDistributionKernel
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceDistributionLocal
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceDistributionMollifyBounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceDistributionSwap
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceDistributionTransport
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceGradientBumps
set_option autoImplicit false
set_option warningAsError true
/-!
# From a countable family of mollifier bumps to every test function

A distributional identity that is only known against a *countable* family of
test functions can be upgraded to all test functions when the family is rich
enough.  The family used here is the family of mollifier bumps
`x ↦ mollifier (sliceRadius n) (x - y)` centred at the points `y` of a dense
set.  The upgrade has three steps.

* The pairing of a locally integrable field with a translated bump depends
  continuously on the centre, so vanishing on a dense set of centres gives
  vanishing at every admissible centre.
* Integrating the resulting identity against a test function `ψ` and exchanging
  the order of integration replaces the bump by the mollification of the
  transform of `ψ` that appears in the pairing.
* Letting the radius tend to zero recovers that transform itself.

The argument is carried out once, for an abstract kernel family `κ` and an
abstract transform `T` of the test function, and then specialised to the two
pairings used in `paper/ckn.tex`: the spatial divergence pairing
`∑ᵢ gᵢ ∂ᵢψ` and the plain multiplication pairing `F ψ`.  This is the mechanism
behind the almost-everywhere slice identities there: the null set produced by
testing one test function at a time is replaced by a single null set valid for
every test function.
-/
open MeasureTheory Metric Filter Topology Set
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end
