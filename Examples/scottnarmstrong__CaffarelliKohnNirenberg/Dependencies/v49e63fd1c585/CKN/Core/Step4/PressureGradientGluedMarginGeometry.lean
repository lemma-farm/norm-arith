-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Harmonic.KernelAllOrdersShift
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Topology
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.BallDisplays
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Statements.SpaceTimeSet
set_option autoImplicit false
set_option warningAsError true
/-!
# Margin-safe parabolic cylinders and their closures

This file records the elementary geometry behind the "doubling with a margin"
step: a parabolic cylinder that meets the carrier region and whose radius is at
most one third of the margin separating the carrier from the outer ball has its
doubled-radius cylinder, and hence the closure of that cylinder, contained in
the outer region.  This is what lets a slice estimate proved at a single cell
radius be applied at twice that radius, at the price of a third of the gap
between the inner and outer regions.

The results are stated in the two settings used later: a one-sided cylinder
based at the origin of the unit parabolic cylinder, and a parabolic metric ball
about an arbitrary centre.
-/
open MeasureTheory Set
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN.Core.Step4
end CKN.Core.Step4
