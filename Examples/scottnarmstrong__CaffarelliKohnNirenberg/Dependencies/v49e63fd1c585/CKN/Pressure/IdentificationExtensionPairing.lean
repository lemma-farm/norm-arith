-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionPairingSwap
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionPairingWholeSpace
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Identification
set_option autoImplicit false
set_option warningAsError true
/-!
# The identification data for the leading pressure term

The Calderón--Zygmund bound for the leading local pressure `p₁` consumes two
facts about a fixed time slice: the whole-space distributional identity pairing
`p₁(·, s)` with `Δψ` against the tensor source `η U(·, s)`, and the integrability
of that pairing, both for *every* compactly supported smooth spatial test
function `ψ`.  The identity produced by the pressure decomposition holds, for
each fixed `ψ`, only for almost every time, with an exceptional set depending on
`ψ`.  Testing against the countable family of mollifier bumps removes that
dependence, and the two facts below hold, for almost every time, simultaneously
for every test function.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end
