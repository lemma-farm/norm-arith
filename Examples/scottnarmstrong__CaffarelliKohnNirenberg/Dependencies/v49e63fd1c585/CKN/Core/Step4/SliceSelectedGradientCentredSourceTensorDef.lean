-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Core.Step4.SliceSelectedGradientCentredSource
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
/-!
# The force-free centred pressure source

The first pressure potential is paired with the singly centred tensor
`pressureUTensor u c`. Its divergence source contains neither the force term
nor the centring correction. The force remains in the separate `p₇ + p₈`
pressure contribution.
-/
end CKN.Core.Step4
