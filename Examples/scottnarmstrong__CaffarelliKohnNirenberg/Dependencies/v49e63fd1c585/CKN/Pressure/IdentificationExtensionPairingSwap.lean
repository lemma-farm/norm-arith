-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionPairingKernel
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.IdentificationExtensionPairingSource
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceDistributionCore
set_option autoImplicit false
set_option warningAsError true
/-!
# One null set for every second-order test pairing

A second-order distributional identity on time slices is first obtained one test
function at a time, and the exceptional set of times then depends on the test
function.  Testing instead against the countable family of mollifier bumps
centred at the points of a countable dense set produces a single null set, and
the mollifier-bump upgrade recovers every smooth compactly supported test
function from that countable family.  This is the second-order counterpart of
the divergence-form and multiplication-form upgrades used for the slice
identities.
-/
open MeasureTheory Metric Filter Topology Set
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end
