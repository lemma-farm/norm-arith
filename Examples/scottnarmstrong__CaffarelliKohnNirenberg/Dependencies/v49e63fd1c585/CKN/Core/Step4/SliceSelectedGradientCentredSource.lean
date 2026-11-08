-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientSWSUnconditional
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SourceMorreySlice
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
/-!
# The centred divergence-form source for the selected pressure gradient

The source below is the one paired with the singly centred tensor
`pressureUTensor u c`.  The constant vector `c` is spatially constant.  A
force term remains in the source, so its tested identity has an additional
force pairing unless that pairing is separately known to vanish.

The elementary reason for using the centred source is recorded here as a
compiled pointwise probe: with `u ≡ a`, `Du = 0`, `f = 0`, and `c = 0`, the
uncentred source is zero while the centred tensor has a nonzero `(0,0)` entry.
-/
end CKN.Core.Step4
