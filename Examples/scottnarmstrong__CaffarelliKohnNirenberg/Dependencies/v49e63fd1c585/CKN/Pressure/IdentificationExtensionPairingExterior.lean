-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionPairingSource
set_option autoImplicit false
set_option warningAsError true
/-!
# The leading pressure term away from the cut-off

The leading local pressure `p₁ = ηp - (p₂ + ⋯ + p₈)` is built from `ηp` and from
Newtonian potentials whose sources all vanish outside `tsupport η`.  Consequently
`p₁` is harmonic in the sense of distributions outside `tsupport η`: a test
function vanishing on an open neighbourhood of the cut-off support pairs to zero
against `Δp₁`.  This is the exterior half of the whole-space distributional
identity for `p₁`; the interior half is the localized identity of the pressure
decomposition.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end
